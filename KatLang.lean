-- KatLang v0.73 (core AST + semantics + double-parens grouping + load elaboration)
-- Core semantics are authoritative. Surface syntax handled externally except
-- where noted (implicit parameter detection, double-parens grouping, load).
--
-- Open declarations:
--   `open` is a DECLARATION keyword, not a property assignment.
--   Exact syntax: `open target1, target2, ...` (no `=` sign).
--   Each algorithm may contain at most ONE `open` declaration with a comma-separated
--   list of targets. The opens list maps to `Algorithm.opens : List Expr`.
--
--   Valid open targets (post-elaboration / canonical forms):
--     - identifier:     `open Math`            → Resolve("Math")
--     - dotted path:    `open Lib.Sub`         → Prop(Resolve("Lib"), "Sub")
--     - load:           `open load('url')`     → Call(Resolve("load"), ...) → elaborated to Block
--     - combine:        `open A; B`            → Combine(Resolve("A"), Resolve("B"))
--     - inline block:   `open (public X = 1)`  → Block(...)
--
--   Exact-syntax sugar (parser-only, not in core model):
--     - `open 'url'` desugars to `open load('url')` before elaboration.
--     Raw string literals do NOT survive into the canonical open list.
--
--   Semantic rules (enforced by evaluator, not parser):
--     - Opens provide PUBLIC properties only (lookupOpens filters by isPublic).
--     - Strict isolation: opening a library does NOT import its transitive opens
--       (combineAlgOpensClosed closes opens).
--     - Ambiguity: if multiple open targets provide the same public name, and no
--       owned/local/parent property shadows it, `ambiguousOpen` is raised.
--     - Owned/local/parent lookup takes precedence over opens (ownership-first).

namespace KatLang

--------------------------------------------------------------------------------
-- Typed identifiers (lightweight aliases for future-proofing)
--------------------------------------------------------------------------------

abbrev Ident := String    -- algorithm / property / parameter names
abbrev Sym   := String    -- symbol literals (nameLiteral)
abbrev Assoc (K V : Type) := List (Prod K V)  -- association list

--------------------------------------------------------------------------------
-- Errors / Monad
--------------------------------------------------------------------------------

inductive Error where
  | unknownName      : Ident -> Error
  | unknownProperty  : String -> Ident -> Error        -- object desc, property name
  | notPublicProperty : String -> Ident -> Error       -- object desc, property name (exists but private)
  | notAnAlgorithm   : String -> Error
  | illegalInOpen    : String -> Error                -- semantic restriction (e.g., builtin not allowed)
  | badOpenForm      : String -> Error                -- syntactic form not allowed in open
  | illegalInEval    : String -> Error                -- not evaluable to a value
  | ambiguousOpen    : Ident -> List String -> Error   -- name, providers
  | arityMismatch    : Nat -> Nat -> Error     -- expected, actual
  | badArity         : Error                   -- shape / unpacking failure
  | badIndex         : Error
  | divByZero        : Error                   -- division or modulo by zero
  | withContext      : String -> Error -> Error -- contextual wrapper
  deriving Repr

abbrev EvalM := Except Error

-- * IMPORTANT: Needed for compiling `partial` definitions.
-- Lean requires `Nonempty` for the function types of partial defs.
instance : Nonempty Error := Nonempty.intro Error.badArity
instance {A : Type} : Nonempty (EvalM A) := Nonempty.intro (Except.error Error.badArity)

--------------------------------------------------------------------------------
-- Operators
--------------------------------------------------------------------------------

inductive BinaryOp where
  | add | sub | mul | div | idiv | mod | pow
  | lt | gt | le | ge | eq | ne
  | and | or | xor
  deriving Repr, BEq, DecidableEq

inductive UnaryOp where
  | minus | not
  deriving Repr

inductive Builtin where
  | «if» | «while» | «repeat» | «atoms»
  deriving Repr, BEq, DecidableEq

def builtinArity : Builtin -> Nat
  | .«if» => 3 | .«while» => 2 | .«repeat» => 3 | .«atoms» => 1

--------------------------------------------------------------------------------
-- Syntax
--------------------------------------------------------------------------------

mutual
  inductive Expr where
    | param   : Ident -> Expr
    | nameLiteral : Sym -> Expr   -- * symbol literal, NOT runtime data
    | num     : Int -> Expr
    | stringLiteral : String -> Expr  -- * string literal, surface-only (load URLs etc.)
    | unary   : UnaryOp -> Expr -> Expr
    | binary  : BinaryOp -> Expr -> Expr -> Expr
    | index   : Expr -> Expr -> Expr
    | self    : Expr
    | combine : Expr -> Expr -> Expr
    | resolve : Ident -> Expr
    | prop    : Expr -> Ident -> Expr
    | block   : Algorithm -> Expr
    | call    : Expr -> Algorithm -> Expr
    | dotCall : Expr -> Ident -> Option Algorithm -> Expr    -- a.f or a.f(args)
    | load    : String -> Expr   -- * surface-only: load('url'), eliminated by elaboration
    deriving Repr

  /-- Property definition with visibility metadata. -/
  structure PropDef where
    name     : Ident
    alg      : Algorithm
    isPublic : Bool
    deriving Repr

  inductive Algorithm where
    | mk :
        (parent     : Option ScopeCtx) ->
        (params     : List Ident) ->
        (opens      : List Expr) ->
        (properties : List PropDef) ->
        (output     : List Expr) ->
        Algorithm
    | builtin : Builtin -> Algorithm
    deriving Repr

  inductive ScopeCtx where
    | mk :
        (parent  : Option ScopeCtx) ->
        (opens   : List Expr) ->
        (props   : List PropDef) ->
        ScopeCtx
    deriving Repr
end

--------------------------------------------------------------------------------
-- Result (structured evaluation artifact)
--------------------------------------------------------------------------------

inductive Result where
  | atom  : Int -> Result
  | group : List Result -> Result
  deriving Repr

namespace Result
  def normalize : Result -> Result
    | atom n => atom n
    | group rs =>
        let rs' := rs.map normalize
        match rs' with
        | [r] => r
        | _   => group rs'

  def atoms : Result -> List Int
    | atom n    => [n]
    | group rs => rs.flatMap atoms

  def asInt? : Result -> Option Int
    | atom n => some n
    | group rs =>
        match normalize (group rs) with
        | atom n => some n
        | _      => none

  /-- Extract top-level items from a result.
      Atom → singleton list; Group → its items. -/
  def toItems : Result -> List Result
    | atom n   => [atom n]
    | group rs => rs

  /-- Structural indexing (preserves grouping). -/
  def index? : Result -> Nat -> Option Result
    | atom n, 0   => some (atom n)
    | atom _, _   => none
    | group rs, i => rs[i]?
end Result

--------------------------------------------------------------------------------
-- Environments
--------------------------------------------------------------------------------

abbrev ValEnv := Assoc Ident Result

/-- Evaluation context threaded through resolution and evaluation.
    Wraps the algorithm chain (current algorithm + enclosing callers) used for
    both lexical resolution and runtime dispatch.  A single-field record today,
    ready to split into separate lexical / runtime stacks for C# codegen. -/
structure EvalCtx where
  callStack : List Algorithm
  deriving Repr

namespace EvalCtx
  def empty : EvalCtx := { callStack := [] }
  def push (a : Algorithm) (ctx : EvalCtx) : EvalCtx :=
    { callStack := a :: ctx.callStack }
  def head? (ctx : EvalCtx) : Option Algorithm := ctx.callStack.head?
end EvalCtx

def lookupAssoc {A} (k : Ident) : Assoc Ident A -> Option A
  | [] => none
  | (k',v)::xs => if k = k' then some v else lookupAssoc k xs

abbrev ValEnv.lookup (env : ValEnv) (x : Ident) : Option Result :=
  lookupAssoc x env

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

/-- Primary helper: Lookup PropDef by name (public only). -/
def lookupPropDefPublic? (ps : List PropDef) (k : Ident) : Option PropDef :=
  ps.find? (fun p => p.name = k && p.isPublic)

/-- Private aliases for backwards compatibility. -/
private def findPropAny? := @lookupPropDefAny?
private def findPropPublic? := @lookupPropDefPublic?

/-- Lookup Algorithm from PropDef list (any visibility). -/
def lookupPropAny (ps : List PropDef) (k : Ident) : Option Algorithm :=
  (lookupPropDefAny? ps k).map (·.alg)

/-- Lookup Algorithm from PropDef list (public only). -/
def lookupPropPublic (ps : List PropDef) (k : Ident) : Option Algorithm :=
  (lookupPropDefPublic? ps k).map (·.alg)

/-- Check if PropDef list contains a property (any visibility). -/
def hasPropAny (ps : List PropDef) (k : Ident) : Bool :=
  (lookupPropDefAny? ps k).isSome

/-- Check if PropDef list contains a public property. -/
def hasPropPublic (ps : List PropDef) (k : Ident) : Bool :=
  (lookupPropDefPublic? ps k).isSome

namespace Algorithm
  def parent : Algorithm -> Option ScopeCtx
    | .mk p _ _ _ _ => p
    | .builtin _ => none
  def params : Algorithm -> List Ident
    | .mk _ ps _ _ _ => ps
    | .builtin _ => []
  def opens : Algorithm -> List Expr
    | .mk _ _ op _ _ => op
    | .builtin _ => []
  def props : Algorithm -> List PropDef
    | .mk _ _ _ pr _ => pr
    | .builtin _ => []
  def output : Algorithm -> List Expr
    | .mk _ _ _ _ out => out
    | .builtin _ => []

  def withParent (p : Option ScopeCtx) : Algorithm -> Algorithm
    | .mk _ ps op pr out => .mk p ps op pr out
    | .builtin b => .builtin b

  def asScopeCtx (a : Algorithm) : ScopeCtx :=
    ScopeCtx.mk (parent a) (opens a) (props a)

  def isBuiltin : Algorithm -> Bool
    | .builtin _ => true
    | _          => false

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

  /-- Wire a child algorithm to its parent's scope context. -/
  def childOf (a : Algorithm) (child : Algorithm) : Algorithm :=
    child.withParent (some (a.asScopeCtx))
end Algorithm

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

/-- Unwired parent-chain lookup: returns the algorithm as stored at its
    definition site, without rewiring its parent to the opener.
    Used exclusively by open resolution to enforce isolation. -/
partial def lookupInParentsDirectUnwired (sc : ScopeCtx) (name : Ident) : Option Algorithm :=
  match lookupPropAny (ScopeCtx.props sc) name with
  | some child => some child
  | none =>
      match ScopeCtx.parent sc with
      | some sc' => lookupInParentsDirectUnwired sc' name
      | none     => none

/-- Unwired direct lexical lookup: same search path as `lookupLexicalDirect`
    but returns algorithms without rewiring to the caller.
    The returned algorithm's parent chain is the one from its definition site.
    Used by `resolveAlgForOpen` to preserve open isolation. -/
partial def lookupLexicalDirectUnwired (a : Algorithm) (name : Ident) : Option Algorithm :=
  match Algorithm.lookupProp a name with
  | some child => some child
  | none =>
    match Algorithm.parent a with
    | some sc => lookupInParentsDirectUnwired sc name
    | none    => none

/-- Public-only unwired parent-chain lookup: returns public properties only.
    Used by open resolution to enforce strict public-only open targets. -/
partial def lookupInParentsDirectUnwiredPublic (sc : ScopeCtx) (name : Ident) : Option Algorithm :=
  match lookupPropPublic (ScopeCtx.props sc) name with
  | some child => some child
  | none =>
      match ScopeCtx.parent sc with
      | some sc' => lookupInParentsDirectUnwiredPublic sc' name
      | none     => none

/-- Public-only unwired direct lexical lookup: searches local then parent chain
    for public properties only, returning algorithms unwired (definition-site parent preserved).
    Used by `resolveAlgForOpen` to enforce strict public-only open targets. -/
partial def lookupLexicalDirectUnwiredPublic (a : Algorithm) (name : Ident) : Option Algorithm :=
  match Algorithm.lookupPublicProp a name with
  | some child => some child
  | none =>
    match Algorithm.parent a with
    | some sc => lookupInParentsDirectUnwiredPublic sc name
    | none    => none

def wireToCaller (ctx : EvalCtx) (a : Algorithm) : Algorithm :=
  match ctx.callStack.head? with
  | some caller => Algorithm.childOf caller a
  | none        => a

--------------------------------------------------------------------------------
-- Intrinsics
--------------------------------------------------------------------------------

/-- Predicate for intrinsic (non-builtin) property names.
    These names are handled specially in resolveAlg / evalProp / evalDotCall
    rather than being looked up as structural properties. -/
def isIntrinsic (name : Ident) : Bool :=
  name = "length"

/-- Evaluate an intrinsic property on a resolved algorithm.
    Returns `some result` if `name` is a recognized intrinsic, `none` otherwise.
    Single source of truth for intrinsic semantics. -/
def evalIntrinsic? (targetAlg : Algorithm) (name : Ident) : EvalM (Option Result) :=
  if name = "length" then
    pure (some (Result.atom (Int.ofNat (Algorithm.output targetAlg).length)))
  else
    pure none

--------------------------------------------------------------------------------
-- Semantics
--------------------------------------------------------------------------------

/-- Coerce a Result to Int, or raise badArity. -/
def expectInt (r : Result) : EvalM Int :=
  match Result.asInt? r with
  | some n => pure n
  | none   => .error Error.badArity

/-- Step output: state and continuation flag. -/
abbrev StepOut := Prod Result Int

/-- Split a step result into (state, continue-flag).
    Convention: the last atom is the continue flag (nonzero = keep going). -/
def splitCont (out : Result) : EvalM StepOut := do
  match out with
  | .atom n => pure (.atom n, n)
  | .group rs =>
      match rs.getLast? with
      | some last =>
          let c <- expectInt last
          let state := Result.normalize (.group rs.dropLast)
          pure (state, c)
      | none => .error Error.badArity

partial def bindParams (ps : List Ident) (vs : List Result) : EvalM ValEnv :=
  match ps, vs with
  | [], [] => .ok []
  | p::ps', v::vs' => do
      let rest <- bindParams ps' vs'
      pure ((p,v)::rest)
  | _, _ => .error (Error.arityMismatch ps.length vs.length)

/-- Argument passing rule: a single atom is wrapped in a one-element list;
    a group is unpacked into its elements.  This is the canonical ABI for
    translating an evaluated Result into positional arguments for bindParams. -/
def unpackArgs (r : Result) : List Result :=
  match r with
  | .atom _ => [r]
  | .group rs => rs

/-- Attach context to any error raised by `m`. -/
def withCtx (ctx : String) (m : EvalM A) : EvalM A :=
  m.mapError (Error.withContext ctx)

def intPow (b : Int) : Nat -> Int
  | 0 => 1
  | n + 1 => b * intPow b n

def combineAlg (a b : Algorithm) : Algorithm :=
  Algorithm.mk
    none
    (a.params ++ b.params)           -- params merged
    (a.opens ++ b.opens)             -- * opens merged
    (a.props  ++ b.props)            -- properties merged
    [ Expr.block a, Expr.block b ]   -- output preserves boundaries

/-- Combine algorithms without merging opens (for open resolution).
    Enforces isolation: libraries cannot smuggle in transitive opens. -/
def combineAlgOpensClosed (a b : Algorithm) : Algorithm :=
  Algorithm.mk
    none
    (a.params ++ b.params)           -- params merged
    []                               -- * opens closed (no transitive open smuggling)
    (a.props  ++ b.props)            -- properties merged
    [ Expr.block a, Expr.block b ]   -- output preserves boundaries

/-- Predicate defining which expression forms are allowed in open position
    **after elaboration**.  Only structural references to libraries are permitted.

    OpenForm is the *post-elaboration* set of permitted open expressions.
    `Expr.load` may appear in source-level open lists, but the load elaboration
    pass MUST rewrite every `Expr.load` into `Expr.block` before open resolution
    or validation runs.  If a buggy caller runs open resolution before load
    elaboration, the `Expr.load` node will fall through to the `none` branch of
    `Expr.openForm?` and be rejected as `badOpenForm`.

    Note: the C# parser produces DotCall for all dot syntax (e.g. `Lib.Sub`).
    A parser-level normalization pass rewrites `DotCall(obj, name, none)` to
    `Prop(obj, name)` in open expressions, and rejects `DotCall(obj, name, some args)`
    as an invalid open form.  After normalization and load elaboration, opens
    contain only the forms listed below.

    Additionally, the exact-syntax sugar `open 'url'` is desugared to
    `open load('url')` at parse time, so raw string literals never appear
    in the canonical open list.  The load elaboration pass then rewrites
    `load('url')` into `Block(parsed module)` as usual. -/
inductive OpenForm where
  | combine : Expr -> Expr -> OpenForm
  | block   : Algorithm -> OpenForm
  | resolve : Ident -> OpenForm
  | prop    : Expr -> Ident -> OpenForm

def Expr.openForm? : Expr -> Option OpenForm
  | .combine a b => some (.combine a b)
  | .block a     => some (.block a)
  | .resolve n   => some (.resolve n)
  | .prop o n    => some (.prop o n)
  | _            => none          -- Expr.load and all other forms are rejected

def Expr.isOpenForm (e : Expr) : Bool :=
  (Expr.openForm? e).isSome

/-- Human-readable constructor kind for diagnostics. -/
def Expr.kind : Expr -> String
  | .param _      => "param"
  | .nameLiteral _ => "nameLiteral"
  | .num _        => "num"
  | .stringLiteral _ => "stringLiteral"
  | .unary _ _    => "unary"
  | .binary _ _ _ => "binary"
  | .index _ _    => "index"
  | .self         => "self"
  | .combine _ _  => "combine"
  | .resolve _    => "resolve"
  | .prop _ _     => "prop"
  | .block _      => "block"
  | .call _ _     => "call"
  | .dotCall _ _ _  => "dotCall"
  | .load _       => "load"

/-- Extract a descriptive name from an open expression for error messages. -/
def openExprName (e : Expr) : String :=
  match e with
  | .resolve n => n
  | .prop o n => openExprName o ++ "." ++ n
  | .dotCall o n _ => openExprName o ++ "." ++ n
  | .block _ => "(inline library)"
  | .combine a b => openExprName a ++ " + " ++ openExprName b
  | .nameLiteral s => s!"'{s}"          -- * render name literals as symbols
  | .load url => s!"load('{url}')"
  | _ => s!"({Expr.kind e})"            -- * informative fallback using constructor kind

namespace CtxMsg
  def «open» (k : String)              := s!"while resolving open: {k}"
  def call   (f : Expr)               := s!"while evaluating call to {openExprName f}"
  def prop   (obj : Expr) (n : Ident) := s!"while evaluating property .{n} of {openExprName obj}"
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

/-- A single hit from open lookup: which provider supplied it, the library, and the child algorithm. -/
structure OpenHit where
  provider : String
  lib      : Algorithm
  child    : Algorithm
  deriving Repr

mutual

  --------------------------------------------------------------------------
  -- Open resolution
  --------------------------------------------------------------------------

  /-- Algorithm resolution using only direct lexical lookup (no opens).
      Used for resolving open expressions to avoid circularity.

      Open resolution returns algorithms without rewiring to the opener.
      The returned algorithm's parent chain is the one from its definition
      site (if any).  This enforces open isolation: a library's internal
      lexical structure is self-contained and never smuggles caller context.

      Open restrictions:
      - Only `Expr.openForm?` forms are permitted (structural references to libraries only).
      - Builtins are rejected: they are not valid open targets.
      - **Public-path policy**: Property access in open paths (e.g., `Open = Lib.Sub`) requires
        all intermediate properties to be public. `Algorithm.lookupPublicProp` enforces this.

      Examples:
      - `open Lib` where `Lib` has `{ publicProp "Sub" ... }` → OK, exposes public properties of Sub
      - `open Lib.PrivateSub` where `PrivateSub` has `isPublic = false` → Error (unknownProperty)
      - Structural access `Lib.PrivateSub.X` in code → OK (uses Algorithm.lookupProp, sees private)
      - `open Lib` does NOT expose private properties of Lib (filtered by lookupOpens) -/
  partial def resolveAlgForOpen (e : Expr) (ctx : EvalCtx) : EvalM Algorithm := do
    match Expr.openForm? e with
    | some (.combine e1 e2) => do
      let a <- resolveAlgForOpen e1 ctx
      let b <- resolveAlgForOpen e2 ctx
      pure (combineAlgOpensClosed a b)  -- * no wiring, no open merging (strict isolation)
    | some (.block a) => pure a       -- * no wiring for opens
    | some (.resolve n) =>
      match ctx.callStack with
      | a::_ =>
        match lookupLexicalDirectUnwiredPublic a n with
        | some r =>
            if r.isBuiltin then .error (Error.illegalInOpen s!"builtin '{n}'")
            else pure r       -- * unwired: preserves definition-site parent chain
        | none =>
            -- Try unfiltered lookup to distinguish private vs missing
            match lookupLexicalDirectUnwired a n with
            | some _ => .error (Error.notPublicProperty "(lexical)" n)
            | none   => .error (Error.unknownName n)
      | [] => .error (Error.unknownName n)
    | some (.prop o n) => do
      let a <- resolveAlgForOpen o ctx
      -- First check if property exists at all to distinguish missing vs private
      match Algorithm.lookupProp a n with
      | some p =>
          if p.isBuiltin then
            .error (Error.illegalInOpen s!"builtin not allowed in open: {openExprName o}.{n}")
          else
            -- Property exists; check if it's public
            match Algorithm.lookupPublicProp a n with
            | some publicAlg => pure publicAlg  -- * no wiring (pure resolution) - return public algorithm
            | none   => .error (Error.notPublicProperty (openExprName o) n)
      | none => .error (Error.unknownProperty (openExprName o) n)
    -- No `.load` case: load is not a valid OpenForm post-elaboration.
    -- If Expr.load reaches here (elaboration was skipped), it falls through to
    -- `none` and is rejected with a clear diagnostic.
    | none =>
        -- Provide a specific message for Expr.load to aid debugging
        match e with
        | .load url => throw (Error.badOpenForm s!"internal error: load must be elaborated before open resolution: {url}")
        | _ => throw (Error.badOpenForm s!"{Expr.kind e}: {openExprName e}")

  /-- Resolve an open expression to a library algorithm. -/
  partial def resolveOpen (e : Expr) (ctx : EvalCtx) : EvalM Algorithm :=
    resolveAlgForOpen e ctx

  /-- Resolve all opens of an algorithm upfront.
      Deduplicates named opens by `openExprName` (first occurrence wins) to
      avoid repeated resolution and spurious ambiguity.  Inline blocks are never
      deduplicated (each gets a unique positional key).
      Validates all open expressions first for fail-fast diagnostics. -/
  partial def resolveAllOpens (a : Algorithm) (ctx : EvalCtx) : EvalM (List ResolvedOpen) := do
    let rawOpens := Algorithm.opens a
    -- Deduplicate by key (first occurrence wins); inline blocks use positional keys
    let tagged := rawOpens.mapIdx (fun idx e =>
      let key := match e with
        | .block _ => s!"(inline#{idx})"   -- * unique per original position, never deduped
        | _        => openExprName e
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
      let lib <- withCtx (CtxMsg.«open» key) (resolveOpen e ctx)
      pure { key := key, expr := e, lib := lib })

  /-- Lookup in opened namespaces with ambiguity error.
      Ordering rule: opens are searched in declaration order (first wins for
      single-provider lookups; multiple providers trigger ambiguousOpen).
      Only public properties are visible through opens.
      Returns:
        * ok none              if no open provides `name` publicly
        * ok (some alg)        if exactly one open provides it publicly (wired to library parent)
        * error ambiguousOpen if multiple opens provide it publicly -/
  partial def lookupOpens (a : Algorithm) (name : Ident) (ctx : EvalCtx) : EvalM (Option Algorithm) := do
    let ctx' := EvalCtx.push a ctx
    let resolvedOpens <- resolveAllOpens a ctx'

    -- * Public-only filtering: only public properties visible through opens
    -- Keys from resolveAllOpens are used directly as provider tags.
    let mut hits : List OpenHit := []
    for ri in resolvedOpens do
      match Algorithm.lookupPublicProp ri.lib name with
      | some child =>
          hits := { provider := ri.key, lib := ri.lib, child := child } :: hits
      | none => pure ()
    hits := hits.reverse

    match hits with
    | [] => pure none  -- No public matches found
    | [h] =>
        pure <| some (Algorithm.childOf h.lib h.child)
    | hs =>
        .error (Error.ambiguousOpen name (hs.map (·.provider)))

  --------------------------------------------------------------------------
  -- Lexical resolution
  --------------------------------------------------------------------------

  /-- Structural-only lookup in parent chain (no opens anywhere).
      Ownership-first model: structural properties take precedence.
      Example: If parent defines Pi and opens Math also exports Pi,
      the parent's Pi wins. To get Math.Pi, use Math.Pi syntax. -/
  partial def lookupInParentsStructural (sc : ScopeCtx) (name : Ident) : Option Algorithm :=
    match lookupPropAny (ScopeCtx.props sc) name with
    | some child => some (Algorithm.withParent (some sc) child)
    | none =>
        match ScopeCtx.parent sc with
        | some sc' => lookupInParentsStructural sc' name
        | none     => none

  /-- Open-based lookup in parent chain (helper for lookupOpensInChain). -/
  partial def lookupOpensInParentChain (sc : ScopeCtx) (name : Ident) (ctx : EvalCtx) : EvalM (Option Algorithm) := do
    let tempAlg := Algorithm.forOpens sc
    match (<- lookupOpens tempAlg name ctx) with
    | some r => pure (some r)
    | none =>
        match ScopeCtx.parent sc with
        | some sc' => lookupOpensInParentChain sc' name ctx
        | none     => pure none

  /-- Open-based lookup across the algorithm chain (current first, then parents).
      Checks opens at each level of the parent chain as fallback. -/
  partial def lookupOpensInChain (a : Algorithm) (name : Ident) (ctx : EvalCtx) : EvalM (Option Algorithm) := do
    -- Try opens at current level
    match (<- lookupOpens a name ctx) with
    | some r => pure (some r)
    | none =>
        -- Try parent chain
        match Algorithm.parent a with
        | some sc => lookupOpensInParentChain sc name ctx
        | none    => pure none

  /-- Full lexical lookup with ownership-first model:
      1. Local properties (owned by this algorithm)
      2. Parent chain structural properties (owned by ancestors)
      3. Opens as fallback (foreign namespaces)

      This ensures structural ownership always takes precedence over opens. -/
  partial def lookupLexical (a : Algorithm) (name : Ident) (ctx : EvalCtx) : EvalM Algorithm := do
    -- 1. local properties
    match Algorithm.lookupProp a name with
    | some child =>
        pure (Algorithm.childOf a child)
    | none =>
        -- 2. parent chain structural only
        match Algorithm.parent a with
        | some sc =>
            match lookupInParentsStructural sc name with
            | some r => pure r
            | none =>
                -- 3. opens fallback across chain
                match (<- lookupOpensInChain a name ctx) with
                | some r => pure r
                | none   => .error (Error.unknownName name)
        | none =>
            -- no parents: try opens fallback
            match (<- lookupOpensInChain a name ctx) with
            | some r => pure r
            | none   => .error (Error.unknownName name)

  partial def resolveAlg (e : Expr) (ctx : EvalCtx) : EvalM Algorithm :=
    match e with
    | .combine e1 e2 => do
        let a <- resolveAlg e1 ctx
        let b <- resolveAlg e2 ctx
        pure (wireToCaller ctx (combineAlg a b))
    | .block a => pure (wireToCaller ctx a)
    | .self =>
        match ctx.head? with
        | some a => pure a
        | none   => .error (Error.notAnAlgorithm "self")
    | .resolve n =>
        match ctx.callStack with
        | a::_ => lookupLexical a n ctx
        | []   => .error (Error.unknownName n)
    | .prop o n =>
        if isIntrinsic n then
          -- Lift intrinsic to wrapper algorithm so it can be passed where Algorithm is expected
          pure (wireToCaller ctx (Algorithm.ofExpr (.dotCall o n none)))
        else do
          let a <- resolveAlg o ctx
          match Algorithm.lookupProp a n with
          | some p =>
            pure (Algorithm.childOf a p)
          | none   => .error (Error.unknownProperty (openExprName o) n)
    | .dotCall o n args =>
        -- Lift a.f / a.f(args) to a wrapper algorithm; evalDotCall handles all semantics
        -- (length intrinsic, structural property, receiver injection, lexical fallback)
        pure (wireToCaller ctx (Algorithm.ofExpr (.dotCall o n args)))
    -- Explicit errors for syntactic forms that cannot resolve to algorithms
    | .param x => .error (Error.notAnAlgorithm s!"param({x})")
    | .nameLiteral s  => .error (Error.notAnAlgorithm s!"nameLiteral({s})")
    | .num n   => .error (Error.notAnAlgorithm s!"num({n})")
    | .unary _ _ => .error (Error.notAnAlgorithm "unary expression")
    | .binary _ _ _ => .error (Error.notAnAlgorithm "binary expression")
    | .index _ _ => .error (Error.notAnAlgorithm "index expression")
    | .call _ _ => .error (Error.notAnAlgorithm "call expression")
    | .load url => .error (Error.illegalInEval s!"load not elaborated: {url}")
    | .stringLiteral s => .error (Error.illegalInEval s!"stringLiteral not elaborated: {s}")

  /-- Resolve argument expressions to algorithms for builtin dispatch.
      Unlike the earlier strict formulation (`mapM resolveAlg`), this function
      wraps *liftable* non-resolvable expressions (`notAnAlgorithm`,
      `illegalInEval`) in trivial `Algorithm.ofExpr` wrappers wired to the
      caller scope.  This enables ergonomic builtin syntax such as
      `If(X >= 5, 1, 0)` without requiring explicit `{…}` blocks around every
      argument.

      Wrapping is safe because builtins evaluate their algorithm arguments
      lazily via `evalAlgOutput`, so the expression is evaluated on demand
      within the correct scope rather than resolved structurally upfront.

      Errors that indicate genuine lookup or semantic failures (`unknownName`,
      `unknownProperty`, `ambiguousOpen`, etc.) are propagated immediately so
      diagnostics remain precise.

      Non-builtin call paths are unaffected — user-defined calls still evaluate
      arguments eagerly through `evalCall`. -/
  partial def resolveArgAlgs (args : Algorithm) (ctx : EvalCtx) : EvalM (List Algorithm) :=
    (Algorithm.output args).mapM (fun e => do
      match resolveAlg e ctx with
      | .ok a    => pure a
      | .error err =>
        if isLiftableError err then
          pure (wireToCaller ctx (Algorithm.ofExpr e))
        else
          .error err)
  where
    isLiftableError : Error → Bool
      | .notAnAlgorithm _ => true
      | .illegalInEval _  => true
      | .withContext _ e   => isLiftableError e
      | _                  => false

  --------------------------------------------------------------------------
  -- Evaluation
  --------------------------------------------------------------------------

  /-- Evaluate an algorithm's output expressions and collect into a single Result.
      Normalization invariant: outputs are always normalized at algorithm boundaries.
      Singleton groups are collapsed here (and only here) so downstream consumers
      never see `group [x]`.  Builtins that synthesize fresh groups (e.g. Atoms)
      must normalize their own output explicitly. -/
  partial def evalAlgOutput (a : Algorithm) (ctx : EvalCtx) (env : ValEnv) : EvalM Result := do
    let rs <- (Algorithm.output a).mapM (fun e => eval e (EvalCtx.push a ctx) env)
    pure (Result.normalize (Result.group rs))

  /-- Evaluate an expression and coerce the result to Int. -/
  partial def evalInt (e : Expr) (ctx : EvalCtx) (env : ValEnv) : EvalM Int := do
    expectInt (<- eval e ctx env)

  /-- Run a step algorithm with the given state bound to its params. -/
  partial def runStep (step : Algorithm) (ctx : EvalCtx) (env : ValEnv) (s : Result) : EvalM Result := do
    let argEnv <- bindParams (Algorithm.params step) (unpackArgs s)
    evalAlgOutput step ctx (argEnv ++ env)

  partial def applyBuiltin
      (b : Builtin) (args : List Algorithm)
      (ctx : EvalCtx) (env : ValEnv)
      : EvalM Result :=
    match b, args with

    | .«if», [c,t,e] => do
        let cr <- evalAlgOutput c ctx env
        match Result.atoms cr with
        | 0::_ => evalAlgOutput e ctx env
        | _::_ => evalAlgOutput t ctx env
        | _    => .error Error.badArity

    | .«while», [step, init] => do
        let s0r <- evalAlgOutput init ctx env
        let rec loop (s : Result) : EvalM Result := do
          let out <- runStep step ctx env s
          let (next, cont) <- splitCont out
          if cont = 0 then pure s else loop next
        pure (<- loop s0r)

    | .«repeat», [step, countAlg, init] => do
        let cr <- evalAlgOutput countAlg ctx env
        let n <- expectInt cr
        if n < 0 then
          .error (Error.illegalInEval "Repeat count must be >= 0")
        else
          let s0r <- evalAlgOutput init ctx env
          let rec repeatLoop (k : Int) (s : Result) : EvalM Result :=
            if k = 0 then pure s else do
              let out <- runStep step ctx env s
              repeatLoop (k-1) out
          repeatLoop n s0r

    | .«atoms», [a] => do
        let r <- evalAlgOutput a ctx env
        let xs := Result.atoms r
        pure (Result.normalize (Result.group (xs.map Result.atom)))

    | _, _ =>
        .error (Error.arityMismatch (builtinArity b) args.length)

  partial def evalProp (obj : Expr) (name : Ident)
      (ctx : EvalCtx) (env : ValEnv) : EvalM Result := withCtx (CtxMsg.prop obj name) do
    let a <- resolveAlg obj ctx
    match (<- evalIntrinsic? a name) with
    | some r => pure r
    | none =>
        match Algorithm.lookupProp a name with
        | some p =>
            evalAlgOutput (Algorithm.childOf a p) ctx env
        | none => .error (Error.unknownProperty (openExprName obj) name)

  /-- Core call dispatch: resolve callee, dispatch builtin vs user-defined.
      Does NOT wrap with context — caller is responsible for withCtx.

      User-defined path: args are wired to the caller's scope via `wireToCaller`
      so that `Expr.resolve` nodes inside arg expressions can resolve names from
      the calling scope (e.g., `F(G)` where G is a property).  Without wiring,
      the args algorithm has no parent and resolution of uppercase identifiers
      (which stay as `Expr.resolve` after the surface pipeline) would fail.
      Builtins already resolve in caller context via `resolveArgAlgs`. -/
  partial def evalCall (f : Expr) (args : Algorithm)
      (ctx : EvalCtx) (env : ValEnv) : EvalM Result := do
    let callee <- resolveAlg f ctx
    match callee with
    | .builtin b => do
        let argAlgs <- resolveArgAlgs args ctx
        applyBuiltin b argAlgs ctx env
    | _ => do
        let wiredArgs := wireToCaller ctx args
        let ar <- evalAlgOutput wiredArgs ctx env
        let argEnv <- bindParams (Algorithm.params callee) (unpackArgs ar)
        evalAlgOutput callee ctx (argEnv ++ env)

  /-- Resolve name lexically and call with receiver prepended to args.
      Delegates to evalCall to get builtin dispatch for free. -/
  partial def callLexicalWithReceiver (name : Ident) (receiver : Expr)
      (extraArgs : Option Algorithm) (ctx : EvalCtx) (env : ValEnv) : EvalM Result := do
    let outputExprs := [receiver] ++ match extraArgs with
      | some ea => Algorithm.output ea
      | none => []
    let combinedArgs := Algorithm.mk none [] [] [] outputExprs
    evalCall (.resolve name) combinedArgs ctx env

  /-- Evaluate dotCall: a.f or a.f(args)
      Smart dispatch:
      - "length" intrinsic → output expression count of target
      - Structural property found (navigation-only):
        - If no args and 0-param → value access
        - If no args and has params → arity mismatch error
        - If args → direct argument binding (no receiver injection)
      - No property → lexical fallback (receiver injection) -/
  partial def evalDotCall (target : Expr) (name : Ident) (argsOpt : Option Algorithm)
      (ctx : EvalCtx) (env : ValEnv) : EvalM Result := do
    let targetAlg <- resolveAlg target ctx
    match (<- evalIntrinsic? targetAlg name) with
    | some r => pure r
    | none =>
        match Algorithm.lookupProp targetAlg name with
        | some p =>
            let wired := Algorithm.childOf targetAlg p
            match argsOpt with
            | none =>
                if (Algorithm.params wired).length = 0 then
                  evalAlgOutput wired ctx env
                else
                  -- Navigation only: no receiver injection, need explicit args
                  .error (Error.arityMismatch (Algorithm.params wired).length 0)
            | some args => do
                -- Navigation only: direct argument binding, no receiver
                let wiredArgs := wireToCaller ctx args
                let ar <- evalAlgOutput wiredArgs ctx env
                let argEnv <- bindParams (Algorithm.params wired) (unpackArgs ar)
                evalAlgOutput wired ctx (argEnv ++ env)
        | none => callLexicalWithReceiver name target argsOpt ctx env

  partial def eval (e : Expr) (ctx : EvalCtx) (env : ValEnv) : EvalM Result :=
    match e with
    | .num n => pure (Result.atom n)

    | .param x =>
        match env.lookup x with
        | some v => pure v
        | none   => .error (Error.unknownName x)

    | .unary op e => do
        let v <- evalInt e ctx env
        pure (Result.atom <|
          match op with
          | .minus => -v
          | .not   => if v = 0 then 1 else 0)

    | .binary op a b => do
        let x <- evalInt a ctx env
        let y <- evalInt b ctx env
        -- Check for division by zero
        if (op == BinaryOp.div || op == BinaryOp.idiv || op == BinaryOp.mod) && y == 0 then
          .error Error.divByZero
        else
          pure (Result.atom <|
            match op with
            | .add  => x + y
            | .sub  => x - y
            | .mul  => x * y
            | .div  => x / y
            | .idiv => x / y
            | .mod  => x % y
            | .pow  => if y < 0 then 0 else intPow x y.toNat
            | .lt   => if x < y then 1 else 0
            | .gt   => if x > y then 1 else 0
            | .le   => if x <= y then 1 else 0
            | .ge   => if x >= y then 1 else 0
            | .eq   => if x = y then 1 else 0
            | .ne   => if x != y then 1 else 0
            | .and  => if x != 0 then (if y != 0 then 1 else 0) else 0
            | .or   => if x != 0 then 1 else (if y != 0 then 1 else 0)
            | .xor  => if x != 0 then (if y = 0 then 1 else 0) else (if y != 0 then 1 else 0))

    | .combine e1 e2 => do
        let r1 <- eval e1 ctx env
        let r2 <- eval e2 ctx env
        pure (Result.normalize (Result.group (r1.toItems ++ r2.toItems)))

    | .block a =>
        evalAlgOutput (wireToCaller ctx a) ctx env

    | .resolve n => do
        let a <- resolveAlg (.resolve n) ctx
        evalAlgOutput a ctx env

    | .prop o n => evalProp o n ctx env

    | .dotCall o n argsOpt => withCtx (CtxMsg.dotCall o n) do
        evalDotCall o n argsOpt ctx env

    -- Call semantics:
    -- 1. Resolve f to an Algorithm
    -- 2. If builtin: args resolved lazily as algorithms, passed to builtin dispatch
    -- 3. If user alg: args evaluated eagerly to values, bound to params
    | .call f args => withCtx (CtxMsg.call f) do
        evalCall f args ctx env

    | .index a i => do
        let ar <- eval a ctx env
        let ir <- eval i ctx env
        let n  <- expectInt ir
        if n < 0 then
          .error Error.badIndex
        else
          match Result.index? ar (Int.toNat n) with
          | some r => pure r
          | none   => .error Error.badIndex

    -- * Catch-all: future-proofing for new Expr constructors.
    -- Uses Expr.kind for clear diagnostics.
    | _ => .error (Error.illegalInEval s!"{Expr.kind e}")

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
    let alg := Algorithm.mk parent params opens knownProps []
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
    The trade-off is accepted: shadowing via opens is rare and explicit (listed in `opens:`). -/
def shouldTreatAsImplicitParam (a : Algorithm) (name : Ident) (ctx : EvalCtx) : EvalM Bool :=
  match lookupLexical a name ctx with
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
   passing the sibling's parameters as arguments (lifted into the referencing
   property's own parameter list).

   Example:
     Surface:   `(A = x + 1;  B = A * 2)`
     After detection: A.params = [x], B.params = []
     After resolution: B.params = [x], B.output = [Call(A, [Param(x)]) * 2]

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
     final parameter list before processing subsequent dependents.

   Cycles are handled by leaving cyclic properties unmodified (no implicit
   argument lifting for properties involved in mutual recursion). -/

--------------------------------------------------------------------------------
-- Surface syntax support: double-parens grouping
--------------------------------------------------------------------------------

/- **Double-parens grouping** is a parser-only transformation that groups
   multiple comma-separated expressions into a single algorithm argument.

   Triggering syntax
   -----------------
   The token pattern `((` ... `))` triggers grouping IF AND ONLY IF it appears
   **in call or dotCall argument position** — i.e., directly inside the
   parenthesized argument list of a call expression:

     f(( e1, e2, ..., ek ))      -- call with grouped arg
     a.g(( e1, e2, ..., ek ))    -- dotCall with grouped arg

   The parser detects this by observing two consecutive opening parentheses
   where a call argument list begins, and two consecutive closing parentheses
   at the end.  The inner parentheses (the second `(` and the first `)`) are
   consumed as grouping delimiters.

   What does NOT trigger double-parens grouping
   ---------------------------------------------
   - `(e1, e2)` in argument position: single parens produce multiple separate
     arguments.  `f(a, b)` passes two arguments, not one grouped argument.
   - `((expr))` outside argument position (e.g., in an output line or property
     RHS): the double parentheses are parsed as redundant expression grouping,
     NOT as a block.  `X = ((1 + 2))` is identical to `X = (1 + 2)` = `X = 3`.
   - Brace blocks `{e1; e2}`: these create a scope boundary with potential
     parameter inference; `((e1, e2))` does NOT create a scope boundary.

   Parser transformation
   ---------------------
   When the parser recognises `(( e1, e2, ..., ek ))` in argument position, it
   emits a single `Expr.block` wrapping a zero-parameter algorithm whose output
   list contains the comma-separated expressions:

     Expr.block(Algorithm.mk(parent: none, params: [], opens: [], props: [],
                             output: [e1, e2, ..., ek]))

   No `tuple` constructor exists in the Lean core AST; grouping is expressed
   purely via `Expr.block`.  No separate desugaring pass is required.

   Free identifiers inside the grouped block bubble up to the enclosing
   algorithm through ParameterDetector (identical treatment to non-parametrized
   call args in single-paren form), because the block has no params of its own.

   Example: while with dotCall
   ---------------------------
   Surface:   `Algo.while((x, 0))`
   Token seq: Algo . while ( ( x , 0 ) )
                            ^-----------^ double-parens detected in arg position
   Parsed AST:
     dotCall(resolve("Algo"), "while",
       argsAlg{ output: [
         block(Algorithm.mk(none, [], [], [], [param(x), num(0)]))
       ]})
   At runtime, dotCall injects receiver:
     while receives [resolve("Algo"), block(initAlg)] → 2 builtin args.

   Contrast (NO grouping):
   Surface:   `Algo.while(x, 0)`
   Parsed AST:
     dotCall(resolve("Algo"), "while",
       argsAlg{ output: [param(x), num(0)] })
   At runtime, dotCall injects receiver:
     while receives [resolve("Algo"), param(x), num(0)] → 3 args → arity mismatch.

   This is why double-parens grouping is essential for passing multi-element
   initial states to builtins like while and repeat via dotCall syntax. -/

--------------------------------------------------------------------------------
-- Entry points
--------------------------------------------------------------------------------

/-- Helper to create a private property (default visibility). -/
def privateProp (name : Ident) (alg : Algorithm) : PropDef :=
  { name := name, alg := alg, isPublic := false }

/-- Helper to create a public property. -/
def publicProp (name : Ident) (alg : Algorithm) : PropDef :=
  { name := name, alg := alg, isPublic := true }

/-- Migration helper: convert assoc list to private PropDefs. -/
def propsPrivate (xs : List (Prod Ident Algorithm)) : List PropDef :=
  xs.map (fun (n, a) => privateProp n a)

/-- Migration helper: convert assoc list to public PropDefs. -/
def propsPublic (xs : List (Prod Ident Algorithm)) : List PropDef :=
  xs.map (fun (n, a) => publicProp n a)

/-- Prelude algorithm providing builtin operations in scope by default.
    Builtins are injected into the initial call stack by adding preludeAlg.
    All builtins are public for use in opened contexts. -/
def preludeAlg : Algorithm :=
  Algorithm.mk none [] []
    [ publicProp "if" (Algorithm.builtin .«if»)
    , publicProp "while" (Algorithm.builtin .«while»)
    , publicProp "repeat" (Algorithm.builtin .«repeat»)
    , publicProp "atoms" (Algorithm.builtin .«atoms»)
    ]
    []

def runResult (e : Expr) : EvalM Result :=
  eval e { callStack := [preludeAlg] } []

def runFlat (e : Expr) : EvalM (List Int) := do
  pure (Result.atoms (<- runResult e))

--------------------------------------------------------------------------------
-- Core sugar (surface syntax is external)
--------------------------------------------------------------------------------

open Expr

def param (s : Ident) : Expr := .param s
def name (s : Sym) : Expr := .nameLiteral s
def num (n : Int) : Expr := .num n
def index (a i : Expr) : Expr := .index a i
def resolve (n : Ident) : Expr := .resolve n
def prop (o : Expr) (n : Ident) : Expr := .prop o n
def block (a : Algorithm) : Expr := .block a
def call (f : Expr) (a : Algorithm) : Expr := .call f a
def dotCall (o : Expr) (n : Ident) : Expr := .dotCall o n none
def self : Expr := .self
def combine (a b : Expr) : Expr := .combine a b

/-- Convenience constructor for algorithms with private properties by default.
    To make properties public, use `publicProp` when building the props list. -/
def alg (ps : List Ident) (op : List Expr) (props : List PropDef) (out : List Expr) : Algorithm :=
  Algorithm.mk none ps op props out

/-- Convenience constructor accepting (name, alg) pairs as private properties. -/
def algPrivate (ps : List Ident) (op : List Expr) (props : List (Prod Ident Algorithm)) (out : List Expr) : Algorithm :=
  Algorithm.mk none ps op (propsPrivate props) out

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
  fetch        : String -> Option String   -- abstract; in C# this is Func<string,string>

/-- Positions where load is allowed (compile-time only).
    load is a directive, not a runtime expression. -/
inductive LoadPosition where
  | propertyDef : LoadPosition   -- RHS of Name = load('...')
  | openList    : LoadPosition   -- inside open load('...') or open target1, target2
  deriving Repr, BEq

/- **load elaboration judgment**

  The elaboration pass transforms surface `Expr.load url` nodes into
  `Expr.block (parseModule (fetch url))` nodes. It enforces:

  1. **Literal URL**: The URL must be a compile-time string literal.
     `call (resolve "load") (alg with output = [stringLiteral url])` is the
     surface parse form; the elaborator extracts the URL from the stringLiteral.

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
  the resulting AST contains NO `Expr.load` or `Expr.stringLiteral` nodes.
  All load directives have been replaced with `Expr.block` containing the
  parsed and elaborated remote algorithm. The evaluator never sees load nodes.

  Formally:
    elaborate(load(url)) = block(parseModule(fetch(url)))
    ∀ e ∈ elaborated AST, e ≠ Expr.load _ ∧ e ≠ Expr.stringLiteral _
-/
mutual
partial def loadInvariant_noLoad : Expr -> Bool
  | .load _          => false
  | .stringLiteral _ => false
  | .unary _ e       => loadInvariant_noLoad e
  | .binary _ a b    => loadInvariant_noLoad a && loadInvariant_noLoad b
  | .index a b       => loadInvariant_noLoad a && loadInvariant_noLoad b
  | .combine a b     => loadInvariant_noLoad a && loadInvariant_noLoad b
  | .prop a _        => loadInvariant_noLoad a
  | .call f args     => loadInvariant_noLoad f && loadInvariant_noLoadAlg args
  | .dotCall a _ args =>
      loadInvariant_noLoad a &&
      match args with
      | some alg => loadInvariant_noLoadAlg alg
      | none => true
  | .block alg       => loadInvariant_noLoadAlg alg
  | _                => true  -- param, nameLiteral, num, self, resolve

partial def loadInvariant_noLoadAlg : Algorithm -> Bool
  | .builtin _ => true
  | .mk _ _ opens props output =>
      opens.all loadInvariant_noLoad &&
      props.all (fun p => loadInvariant_noLoadAlg p.alg) &&
      output.all loadInvariant_noLoad
end

end KatLang
