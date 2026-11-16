import KatLangArityLaws.RuntimeAlias
import KatLangArityLaws.AlgorithmProjectionGuards

open KatLang KatLang.CallReferenceGuards KatLang.AlgorithmProjectionGuards

/-!
# META-S3-2 guards: runtime-target callable aliases on whole programs

Every guard runs a whole program through the authoritative `runResult`: the alias chase
(`resolveAliasChase`, `runtimeAliasStepWith`), the binding cell (`aliasBindingCell`), the VALUE chase and
the bare read (`resolveAliasValueTarget`, `aliasValue`), and since M4★ (ALIAS-UNIFY-1) the value view
(`valueViewCell?`) and the target publication origin (`aliasOriginBinding?`). They are executable
evidence for what `KatLangArityLaws/RuntimeAlias.lean` states over the total definitions. Heap observations follow `CallReferenceGuards` /
`AlgorithmProjectionGuards`: every execution of `Sq(x) = Id(x * x)` allocates ONE `x * x` cell, the
captured `5` is one cell, and every execution of `MkC(t) = Id(Capture(Coll(t)))` allocates ONE
`Capture(Coll(t))` cell, so those counts are execution counts.
-/

namespace KatLang.RuntimeAliasGuards

def alias (target : Expr) : Algorithm := .alias none [] [] target

/-- `Coll(*xs) = xs`, `MkC(t) = Id(Capture(Coll(t)))`, `UseA(f) = { A = f ⏎ A(9) }`,
    `G(o) = o + 100`, `Box10 = { G(x) = x * 10 }`, `UseB(b) = { A = b.G ⏎ A(3) }`,
    `LibK(*xs) = { public K = 99 ⏎ 0 }`, `K(v) = 7`, `Navigate(f) = f.K`,
    `UseN(f) = { A = f ⏎ Navigate(A) }`. -/
def extraRA : List (Ident × Algorithm) :=
  [("Coll", algWithParameters [{ name := "xs", kind := .collecting }] [] [] [.param "xs"]),
   ("MkC", alg ["t"] [] [] [callN "Id" [callN "Capture" [callN "Coll" [.param "t"]]]]),
   ("UseA", algPrivate ["f"] [] [("A", alias (.param "f"))] [callN "A" [.num 9]]),
   ("G", alg ["o"] [] [] [add (.param "o") (.num 100)]),
   ("Box10", algPrivate [] [] [("G", alg ["x"] [] [] [mul (.param "x") (.num 10)])] []),
   ("UseB", algPrivate ["b"] [] [("A", alias (.dotCall (.param "b") "G" none))] [callN "A" [.num 3]]),
   ("LibK", algWithParameters [{ name := "xs", kind := .collecting }] []
      [publicProp "K" (alg [] [] [] [.num 99])] [.num 0]),
   ("K", alg ["v"] [] [] [.num 7]),
   ("Navigate", alg ["f"] [] [] [.dotCall (.param "f") "K" none]),
   ("UseN", algPrivate ["f"] [] [("A", alias (.param "f"))] [callN "Navigate" [.resolve "A"]])]

def runRA (decls : List (Ident × Algorithm)) (rows : List Expr) : Except Error Result :=
  run (extraRA ++ decls) rows

def heapRA (decls : List (Ident × Algorithm)) (rows : List Expr) : Array NeedCell :=
  heap (extraRA ++ decls) rows

/-- `A = R.Algorithm` over `R = Capture(Sq(5))`, `B = A`. -/
def aliasR : List (Ident × Algorithm) := refR ++ [("A", alias (algorithm R)), ("B", alias (.resolve "A"))]

/-! ## D1 — a runtime alias calls the identity the run supplies -/

-- A parameter row: the supplied `Sq`.
#guard valueIs (runRA [] [callN "UseA" [.resolve "Sq"]]) (.atom 81)
-- An `.Algorithm` row and a chain link: fresh calls of the captured callee.
#guard valueIs (runRA aliasR [callN "A" [.num 9]]) (.atom 81)
#guard valueIs (runRA aliasR [callN "B" [.num 3]]) (.atom 9)
-- A parameter-rooted member path on a structural hit: the member `Box10` declares, never the lexical `G`.
#guard valueIs (runRA [] [callN "UseB" [.resolve "Box10"]]) (.atom 30)
-- Higher-order transport and callbacks.
#guard valueIs (runRA aliasR [callN "Ap" [.resolve "A", .num 7]]) (.atom 49)
#guard valueIs (runRA aliasR [.dotCall (.listLiteral [.num 1, .num 2]) "map" (some [.resolve "A"])])
  (.listValue [.atom 1, .atom 4])

/-! ## D3 — a fresh call with exactly the written new supply -/

-- `A(8)` runs `Sq` once over the new `8`; the captured `5` is never supplied.
#guard cellsOf (heapRA aliasR [callN "A" [.num 8]]) xx == 1
#guard cellsOf (heapRA aliasR [callN "A" [.num 8]]) (.num 5) == 0

/-! ## Absence is the value view; failure is never absence -/

-- A parameter bound to a value supplies no identity: `A(9)` is the value view's own arity rejection.
#guard isArity (runRA [] [callN "UseA" [.num 5]]) 0 1
-- On a structural miss `b.G` is a computed value: the alias is its value view.
#guard isArity (runRA [] [callN "UseB" [.num 5]]) 0 1
-- A non-reference receiver is the projection's FAILURE, with its kind.
#guard isTypeMismatchAny (runRA [("R5", alg [] [] [] [.num 5]), ("A5", alias (algorithm (.resolve "R5")))]
  [callN "A5" [.num 9]])

/-! ## VALUE and CALLABLE share ONE binding cell, and so one receiver -/

def aliasMkC : List (Ident × Algorithm) := [("AC", alias (algorithm (callN "MkC" [.num 5]))), ("BC", alias (.resolve "AC"))]

def captureCell : Expr := callN "Capture" [callN "Coll" [.param "t"]]

-- Bare `AC` is the callee read as a value (`Coll` is `[]`), `AC(7, 8)` a fresh call; the receiver
-- `MkC(5)` runs ONCE for both channels, through ONE binding cell.
#guard valueIs (runRA aliasMkC [.listLiteral [.resolve "AC", callN "AC" [.num 7, .num 8]]])
  (.listValue [.listValue [], .listValue [.atom 7, .atom 8]])
#guard cellsOf (heapRA aliasMkC [.listLiteral [.resolve "AC", callN "AC" [.num 7, .num 8]]]) captureCell == 1
#guard cellsOf (heapRA aliasMkC [.listLiteral [.resolve "AC", callN "AC" [.num 7, .num 8]]])
  (algorithm (callN "MkC" [.num 5])) == 1
-- The other channel order, and a chain link's bare read through the same cell.
#guard cellsOf (heapRA aliasMkC [.listLiteral [callN "AC" [.num 7], .resolve "AC", .resolve "BC"]]) captureCell == 1

/-! ## Transport reads the target's members -/

#guard valueIs (runRA [] [callN "UseN" [.resolve "LibK"]]) (.atom 99)

/-! ## A runtime re-entry is a demand cycle, never a loop -/

#guard isCycle (runRA [("A", alias (algorithm R)), ("R", alg [] [] [] [callN "Capture" [callN "A" [.num 1]]])]
  [callN "A" [.num 2]])

/-! ## A shared declaration keeps its distinct declaring namespaces -/

def sharedRuntimeAlias : Algorithm :=
  .alias none [] [] (algorithm (.resolve "R")) (some (.shared 90001))

def runtimeAliasHolder (callee : Ident) : Algorithm := alg [] []
  [publicProp "R" (alg [] [] [] [callN "Capture" [callN callee [.num 5]]]),
   publicProp "A" sharedRuntimeAlias] []

-- The SAME alias declaration, wired under two unactivated scopes with different local R bindings:
-- the second call must resolve Inc, not reuse the first holder's Sq binding cell. C# host-DAG twin:
-- RuntimeCallableAliasMechanismTests.ASharedDeclaration_KeepsEachDeclaringNamespacesBindingCell.
#guard valueIs (runRA [("Box1", runtimeAliasHolder "Sq"), ("Box2", runtimeAliasHolder "Inc")]
  [.call (.dotCall (.resolve "Box1") "A" none) [.num 3],
   .call (.dotCall (.resolve "Box2") "A" none) [.num 3]])
  (.sequenceValue [.atom 9, .atom 4])

/-! ## L-RUN (M4★): a computed target is established ONCE (per its property-lifetime key); calls are fresh

`AT4 = Mk4(5).Algorithm` captures `Z4()` (a ZERO-parameter callee: since M4★ a callable target forwards
at every arity, so `AT4()` is a fresh `Z4()`, never D4's terminal property). Every execution of Mk4's
body allocates ONE `terminalCapture` cell, so its count is the number of receiver executions: the
binding cell (and with it the link's one receiver) is established once for the run whatever observes
it first — a call, a bare read, a chain link — and never again (formerly D4 re-evaluated the row for
every later terminal call). `AT4` is a root property, hence exported: ONE cell per run
(§ ALIAS-CELL-LIFETIME below). -/

def terminalCapture : Expr := callN "Capture" [callN "Z4" []]
def terminalDecls : List (Ident × Algorithm) :=
  [("Z4", alg [] [] [] [.num 42]),
   ("Mk4", alg ["t"] [] [] [callN "Id" [terminalCapture]]),
   ("AT4", alias (algorithm (callN "Mk4" [.num 5]))),
   ("BT4", alias (.resolve "AT4"))]

#guard valueIs (runRA terminalDecls [callN "AT4" []]) (.atom 42)
#guard cellsOf (heapRA terminalDecls [callN "AT4" []]) terminalCapture == 1
#guard cellsOf (heapRA terminalDecls [callN "AT4" [], callN "AT4" []]) terminalCapture == 1
#guard cellsOf (heapRA terminalDecls [.resolve "AT4", callN "AT4" []]) terminalCapture == 1
#guard cellsOf (heapRA terminalDecls [callN "AT4" [], .resolve "AT4"]) terminalCapture == 1
#guard cellsOf (heapRA terminalDecls [.resolve "AT4", .resolve "AT4"]) terminalCapture == 1
#guard cellsOf (heapRA terminalDecls
  [callN "BT4" [], .resolve "AT4", callN "BT4" [], .resolve "AT4", callN "AT4" []]) terminalCapture == 1
#guard valueIs (runRA terminalDecls [.listLiteral [callN "BT4" [], .resolve "AT4", callN "BT4" []]])
  (.listValue [.atom 42, .atom 42, .atom 42])
-- Arity rejects a structural miss without evaluating its fallback VALUE.
#guard isArity (runRA [] [callN "UseB" [.num 5]]) 0 1

/-! ## RF1 R2 (M4★): a braced carrier is its own namespace; references open their target -/

-- `B = { public K = 10 ⏎ A }` is a CARRIER (written braces): `open B` imports its own public K.
def namespaceOuter : Algorithm := algPrivate ["n"] []
  [("A", alias (.param "n")),
   ("B", .alias none [] [publicProp "K" (alg [] [] [] [.num 10])] (.resolve "A") none false),
   ("P", alg [] [.resolve "B"] [] [.resolve "K"])] [.resolve "P"]
#guard valueIs (run [("RFOuter", namespaceOuter)] [callN "RFOuter" [.num 1]]) (.atom 10)

-- B precedes A as in the forward-reference source control; only B's own public K is imported.
def namespaceForward : Algorithm := algPrivate ["n"] []
  [("B", .alias none [] [publicProp "K" (alg [] [] [] [.num 10])] (.resolve "A") none false),
   ("A", alias (.param "n")),
   ("P", alg [] [.resolve "B"] [] [.resolve "K"])] [.resolve "P"]
#guard valueIs (run [("RFOuter", namespaceForward)] [callN "RFOuter" [.num 1]]) (.atom 10)
-- Every alias that reaches the provider rule is its own namespace (carriers and runtime references);
-- a static reference is normalized to its target first (`openStructure`).
#guard !(alias (.resolve "Sq")).requiresArguments
-- So `open A` with `A = Sq` refuses Sq itself (a parameterized provider) once a name lookup
-- reaches the open...
#guard match run [("A", alias (.resolve "Sq")), ("P", alg [] [.resolve "A"] [] [.resolve "MissingOpened"])]
    [.resolve "P"] with
  | .error e => match innermost e with | .illegalInOpen _ => true | _ => false
  | .ok _ => false
-- ...while `open A` with `A = LibQ` opens LibQ's own public members (OD-C).
#guard valueIs (run [("LibQ", alg [] [] [publicProp "KQ" (alg [] [] [] [.num 99])] []),
    ("A", alias (.resolve "LibQ")), ("P", alg [] [.resolve "A"] [] [.resolve "KQ"])] [.resolve "P"])
  (.atom 99)

def namespaceOpened : Algorithm := algPrivate ["n"] []
  [("A", alias (.param "n")),
   ("Lib", alg [] [] [publicProp "Ref" (alias (.resolve "A"))] []),
   ("B", .alias none [.resolve "Lib", .resolve "Lib"]
      [publicProp "K" (alg [] [] [] [.num 10])] (.resolve "Ref") none false),
   ("P", alg [] [.resolve "B"] [] [.resolve "K"])] [.resolve "P"]
#guard valueIs (run [("RFOuter", namespaceOpened)] [callN "RFOuter" [.num 1]]) (.atom 10)

-- A declared Algorithm member is a static alias, never the intrinsic runtime row.
#guard match run
  [("StaticBox", alg [] [] [publicProp "Algorithm" (alias (.resolve "Sq"))] []),
   ("StaticA", alias (.dotCall (.resolve "StaticBox") "Algorithm" none)),
   ("StaticP", alg [] [.resolve "StaticA"] [] [.resolve "MissingStaticMember"])] [.resolve "StaticP"] with
  | .error e => match innermost e with | .illegalInOpen _ => true | _ => false
  | .ok _ => false

-- The ordinary output boundary retains visible empty values and nested sequences.
def terminalEmptyDecls : List (Ident × Algorithm) := terminalDecls.map fun (name, body) =>
  (name, if name == "Z4" then alg [] [] [] [.emptySequence 0] else body)
#guard valueIs (runRA terminalEmptyDecls [.listLiteral [callN "AT4" [], .resolve "AT4", callN "AT4" []]])
  (.listValue [.sequenceValue [], .sequenceValue [], .sequenceValue []])
#guard cellsOf (heapRA terminalEmptyDecls [callN "AT4" [], .resolve "AT4", callN "AT4" []]) terminalCapture == 1

/-! ## Structure first (M4★): a carrier's own member never resolves its forwarding target

`AT4 = { public K = 7 ⏎ Mk4(5).Algorithm }` is a CARRIER: `Nav4(AT4)` transports the carrier itself
(its STRUCTURE) and reads its own `K` WITHOUT establishing the binding cell — no receiver work at all;
the first observation that needs the target (a call or a bare read) establishes it once. -/
def terminalNavigationDecls : List (Ident × Algorithm) :=
  (terminalDecls.map fun (name, body) => (name,
    if name == "AT4" then
      match body with
      | .alias p op _ target id _ => .alias p op [publicProp "K" (alg [] [] [] [.num 7])] target id false
      | _ => body
    else body)) ++ [("Nav4", alg ["f"] [] [] [.dotCall (.param "f") "K" none])]
#guard valueIs (runRA terminalNavigationDecls [callN "Nav4" [.resolve "AT4"], callN "AT4" []])
  (.sequenceValue [.atom 7, .atom 42])
#guard cellsOf (heapRA terminalNavigationDecls [callN "Nav4" [.resolve "AT4"]]) terminalCapture == 0
#guard cellsOf (heapRA terminalNavigationDecls
  [callN "Nav4" [.resolve "AT4"], callN "Nav4" [.resolve "AT4"]]) terminalCapture == 0
#guard cellsOf (heapRA terminalNavigationDecls [callN "Nav4" [.resolve "AT4"], callN "AT4" []]) terminalCapture == 1
#guard cellsOf (heapRA terminalNavigationDecls [callN "Nav4" [.resolve "AT4"], .resolve "AT4"]) terminalCapture == 1
#guard cellsOf (heapRA terminalNavigationDecls
  [callN "Nav4" [.resolve "AT4"], callN "AT4" [], .resolve "AT4"]) terminalCapture == 1
#guard cellsOf (heapRA terminalNavigationDecls
  [callN "Nav4" [.resolve "AT4"], .resolve "AT4", callN "AT4" []]) terminalCapture == 1

/-! ## RF1 (M4★): a carrier's target is resolved at its DECLARING activation

`LocalUse(n) = { A = { R = KeepRef(n, Capture(Z4())) ⏎ R.Algorithm }; A(), A, A(), A }`. KeepRef's first
argument makes R local to n; each execution of R allocates exactly one terminalCapture cell. The carrier
A's forwarding target is established ONCE in A's declaring binding context (one LocalUse call): every
`A()` is a fresh `Z4()` and every bare `A` reads the same binding cell, so R executes ONCE. The ordinary
`+ 0` control is a property: each explicit `A()` enters A's body freshly (CACHE-OWNER-D1) and so reads
R in a fresh activation — TWICE. -/

def localR4 : Algorithm := alg [] [] [] [callN "KeepRef4" [.param "n", terminalCapture]]
def localCacheAlias4 : Algorithm := .alias none []
  [privateLocalProp "R4" (.localCapturedAncestorParams ["n"]) localR4] (algorithm (.resolve "R4")) none false
def localCacheControl4 : Algorithm := alg [] []
  [privateLocalProp "R4" (.localCapturedAncestorParams ["n"]) localR4]
  [add (algorithm (.resolve "R4")) (.num 0)]
def localCacheDecls4 (body : Algorithm) : List (Ident × Algorithm) :=
  [("Z4", alg [] [] [] [.num 42]),
   ("KeepRef4", alg ["unused", "reference"] [] [] [.param "reference"]),
   ("LocalUse4", alg ["n"] []
      [privateLocalProp "A4" (.localCapturedAncestorParams ["n"]) body]
      [callN "A4" [], .resolve "A4", callN "A4" [], .resolve "A4"])]
def localCacheExecutions4 (body : Algorithm) : Nat :=
  cellsOf (heapRA (localCacheDecls4 body) [callN "LocalUse4" [.num 5]]) terminalCapture
#guard localCacheExecutions4 localCacheControl4 == 2
#guard localCacheExecutions4 localCacheAlias4 == 1

/-! ## OD-E / R-6 (M4★): an alias owns no entry; an explicit call publishes under its TARGET

Inspect the cache after the invocation alone: a constant result without this state observation
would not distinguish publication from a later independent bare evaluation. -/

def publicationState4 (decls : List (Ident × Algorithm)) (rows : List Expr) : Except Error Result × EvalState :=
  (runResultM (CallReferenceGuards.program (extraRA ++ decls) rows)).runState EvalState.empty

def entries4 (state : EvalState) (name : Ident) : List CountedResult :=
  (state.zeroArgPropertyCache.filter (fun entry => entry.fst.propertyName == name)).map (·.snd)

-- `AT4()` is the fresh `Z4()` whose origin is the captured callee `Z4` (R-6): Z4's empty entry is
-- established, the alias owns none.
#guard let (result, state) := publicationState4 terminalDecls [callN "AT4" []]
  valueIs result (.atom 42) && (entries4 state "AT4").isEmpty && entries4 state "Z4" == [(.atom 42, 1)]
    && state.activeZeroArgProperties.isEmpty
-- A chain link publishes under the same target.
#guard let (result, state) := publicationState4 terminalDecls [callN "BT4" []]
  valueIs result (.atom 42) && (entries4 state "BT4").isEmpty && (entries4 state "AT4").isEmpty
    && entries4 state "Z4" == [(.atom 42, 1)] && state.activeZeroArgProperties.isEmpty
#guard cellsOf (heapRA terminalDecls
  [callN "AT4" [], .resolve "AT4", callN "AT4" [], .resolve "AT4"]) terminalCapture == 1

-- Coll declares a collecting parameter and accepts zero supplied slots: the fresh `Coll()` through the
-- runtime alias AC publishes under Coll (its target), never under AC.
#guard let (result, state) := publicationState4 aliasMkC [callN "AC" []]
  valueIs result (.listValue []) && (entries4 state "AC").isEmpty
    && entries4 state "Coll" == [(.listValue [], 1)] && state.activeZeroArgProperties.isEmpty

/-! ## ALIAS-CELL-LIFETIME (November 2026): the binding cell has its PROPERTY's lifetime

Owner decision 2026-11-15 (adversarial audit of 2026-11-14, §1.7 and SPECS §9/§10): a runtime alias's
binding cell lives exactly as long as the zero-argument cache entry of the same row written as a
property would (`aliasBindingCellKey`). An alias whose own property is EXPORTED has ONE cell per run;
a LOCAL-ONLY one has one cell per declaring binding context, which property-style reads inherit and
explicit calls replace. The exposure is the front end's classification — an INPUT, written on each
`PropDef` here exactly as the encoder emits it. Formerly the key carried the declaring chain's
ACTIVATIONS, so a property-style read (which records an activation that only inherits the binding
context) established a second cell, and an unrelated local-only sibling — which decides whether a
parameterless owner records an activation at all — changed how explicit calls shared the cell. The
observations: the value, the number of recorded binding cells (`EvalState.aliasCells`), the `tick()`
count, and — for a computed receiver — the receiver's executions (`terminalCapture` cells). The same
programs run as encoder-derived differential cases (`runtime-alias-cell-*` in `LanguageSpecCases.lean`). -/

def tickCall : Expr := callN "tick" []

/-- A run's value, its number of recorded binding cells and its `tick()` count. -/
def lifetimeOf (decls : List (Ident × Algorithm)) (rows : List Expr) : Option (Result × Nat × Nat) :=
  let (result, state) := publicationState4 decls rows
  match result with
  | .ok value => some (value, state.aliasCells.length, state.tickCounter)
  | .error _ => none

/-- `B = { public A = b.GT ⏎ A + 0 }`: `A` reads the enclosing `b`, so `A` — and with it `B` — is
    LOCAL-ONLY. -/
def localB : Algorithm := alg [] []
  [publicLocalProp "A" (.localCapturedAncestorParams ["b"]) (alias (.dotCall (.param "b") "GT" none))]
  [add (.resolve "A") (.num 0)]

/-- `GT(x) = tick() + x * 0`, `FL(b) = { B = { public A = b.GT ⏎ A + 0 } ⏎ rows }`. -/
def localDecls (rows : List Expr) : List (Ident × Algorithm) :=
  [("GT", alg ["x"] [] [] [add tickCall (mul (.param "x") (.num 0))]),
   ("FL", alg ["b"] [] [privateLocalProp "B" (.localCapturedAncestorParams ["b"]) localB] rows)]

def readB : Expr := .resolve "B"
def memberA : Expr := .dotCall (.resolve "B") "A" none

-- spec1: `B.A, B` — the structural path and the property-style read of the owner are ONE declaring
-- context, hence one cell and one `tick()` (formerly `(1, 2)`: the read's own activation had its own cell).
#guard lifetimeOf (localDecls [memberA, readB]) [callN "FL" [.num 5]]
  == some (.sequenceValue [.atom 1, .atom 1], 1, 1)
-- The other order.
#guard lifetimeOf (localDecls [readB, memberA]) [callN "FL" [.num 5]]
  == some (.sequenceValue [.atom 1, .atom 1], 1, 1)
-- spec3: `B, B, B.A, B.A, B(), B.A` — reads share the declaring context's cell, the explicit `B()` binds
-- a fresh context and gets a fresh cell, and the later `B.A` reads the declaring one again
-- (formerly `(1, 1, 2, 2, 3, 2)`).
#guard lifetimeOf (localDecls [readB, readB, memberA, memberA, callN "B" [], memberA]) [callN "FL" [.num 5]]
  == some (.sequenceValue [.atom 1, .atom 1, .atom 1, .atom 1, .atom 2, .atom 1], 2, 2)
-- A LOCAL-ONLY alias stays one cell per explicit call (CACHE-OWNER-D1), and per call of `FL`.
#guard lifetimeOf (localDecls [callN "B" [], callN "B" []]) [callN "FL" [.num 5]]
  == some (.sequenceValue [.atom 1, .atom 2], 2, 2)
#guard lifetimeOf (localDecls [memberA, readB]) [callN "FL" [.num 5], callN "FL" [.num 7]]
  == some (.sequenceValue [.sequenceValue [.atom 1, .atom 1], .sequenceValue [.atom 2, .atom 2]], 2, 2)

/-- `A = Mk4(5).Algorithm`: the row reads no enclosing input, so `A` is EXPORTED. Every execution of
    the receiver `Mk4(5)` allocates one `terminalCapture` cell. -/
def exportedLink : Algorithm := alias (algorithm (callN "Mk4" [.num 5]))

/-- `OuterE(k) = { A = Mk4(5).Algorithm ⏎ A() }` (e4), `OuterP(k) = { public A = Mk4(5).Algorithm ⏎ A() }`
    (esc), `FE2(k) = { Outer = { A = Mk4(5).Algorithm ⏎ A() } ⏎ Outer(), Outer() }` (e2) and `FE3`, which is
    `FE2` with the unused local-only sibling `U = k + 0` as `Outer`'s first declaration (e3). -/
def exportedDecls : List (Ident × Algorithm) :=
  [("Z4", alg [] [] [] [.num 42]),
   ("Mk4", alg ["t"] [] [] [callN "Id" [terminalCapture]]),
   ("OuterE", algPrivate ["k"] [] [("A", exportedLink)] [callN "A" []]),
   ("OuterP", alg ["k"] [] [publicProp "A" exportedLink] [callN "A" []]),
   ("FE2", alg ["k"] []
      [privateProp "Outer" (algPrivate [] [] [("A", exportedLink)] [callN "A" []])]
      [callN "Outer" [], callN "Outer" []]),
   ("FE3", alg ["k"] []
      [privateProp "Outer" (alg [] []
        [privateLocalProp "U" (.localCapturedAncestorParams ["k"]) (alg [] [] [] [add (.param "k") (.num 0)]),
         privateProp "A" exportedLink]
        [callN "A" []])]
      [callN "Outer" [], callN "Outer" []])]

/-- The value, the receiver executions and the recorded binding cells of an exported-alias program. -/
def exportedObservation (rows : List Expr) : Option (Result × Nat × Nat) :=
  match lifetimeOf exportedDecls rows with
  | some (value, cells, _) => some (value, cellsOf (heapRA exportedDecls rows) terminalCapture, cells)
  | none => none

def twice42 : Result := .sequenceValue [.atom 42, .atom 42]

-- e4: two explicit calls of the owner share the run's ONE cell (formerly two cells, two receiver runs).
#guard exportedObservation [callN "OuterE" [.num 0], callN "OuterE" [.num 0]] == some (twice42, 1, 1)
-- esc: a call of the owner, then the member read from OUTSIDE the owner — the same cell.
#guard exportedObservation [callN "OuterP" [.num 0], .call (.dotCall (.resolve "OuterP") "A" none) []]
  == some (twice42, 1, 1)
#guard exportedObservation [.call (.dotCall (.resolve "OuterP") "A" none) [], callN "OuterP" [.num 0]]
  == some (twice42, 1, 1)
-- e2 and e3: the unused local-only sibling `U` gives `Outer` an activation per explicit call; it no
-- longer changes anything of the alias (formerly e3 had two cells where e2 had one).
#guard exportedObservation [callN "FE2" [.num 0]] == some (twice42, 1, 1)
#guard exportedObservation [callN "FE3" [.num 0]] == some (twice42, 1, 1)
#guard exportedObservation [callN "FE3" [.num 0], callN "FE2" [.num 1], callN "FE3" [.num 2]]
  == some (.sequenceValue [twice42, twice42, twice42], 2, 2)

-- THE KEY ITSELF: an exported alias's key ignores the context, the state and every activation of its
-- declaring chain; a local-only one reads the declaring chain's owner context, and without an
-- activated level the access context (the property cache's own fallback).
def keyedProp (exposure : PropExposure) : PropDef :=
  privateLocalProp "A" exposure ((alias (algorithm R)).withDeclarationId (some (.shared 7)))
def keyedLevel (exposure : PropExposure) (activation : Option Nat) : ScopeCtx :=
  .mk none ["p"] [] [keyedProp exposure] [] [] activation none
def keyedAlias (exposure : PropExposure) (activation : Option Nat) : Algorithm :=
  ((alias (algorithm R)).withDeclarationId (some (.shared 7))).withParent (some (keyedLevel exposure activation))
def twoContexts : EvalState :=
  { lexicalActivations := #[{ values := [], bindingContext := 10 }, { values := [], bindingContext := 20 },
      { values := [], bindingContext := 10 }] }
def accessCtx (context : Nat) : EvalCtx := { callStack := [], bindingContext := context }

#guard aliasCellIsExported (keyedAlias .exported none)
#guard !aliasCellIsExported (keyedAlias (.localCapturedAncestorParams ["p"]) none)
-- No property of its own in the declaring scope: keyed as a local-only alias.
#guard !aliasCellIsExported ((alias (algorithm R)).withDeclarationId (some (.shared 8))
  |>.withParent (some (keyedLevel .exported none)))
#guard aliasBindingCellKey (keyedAlias .exported (some 0)) (accessCtx 1) twoContexts
  == aliasBindingCellKey (keyedAlias .exported (some 1)) (accessCtx 2) EvalState.empty
#guard aliasBindingCellKey (keyedAlias .exported none) (accessCtx 1) twoContexts
  == aliasBindingCellKey (keyedAlias .exported (some 1)) (accessCtx 2) twoContexts
-- Local-only: two activations with ONE binding context (a call and a read of it) share the key; another
-- binding context does not; the activation-qualified chase key still separates all three.
#guard aliasBindingCellKey (keyedAlias (.localCapturedAncestorParams ["p"]) (some 0)) (accessCtx 1) twoContexts
  == aliasBindingCellKey (keyedAlias (.localCapturedAncestorParams ["p"]) (some 2)) (accessCtx 2) twoContexts
#guard aliasBindingCellKey (keyedAlias (.localCapturedAncestorParams ["p"]) (some 0)) (accessCtx 1) twoContexts
  != aliasBindingCellKey (keyedAlias (.localCapturedAncestorParams ["p"]) (some 1)) (accessCtx 1) twoContexts
#guard aliasChaseKey (keyedAlias (.localCapturedAncestorParams ["p"]) (some 0))
  != aliasChaseKey (keyedAlias (.localCapturedAncestorParams ["p"]) (some 2))
-- Local-only on an unactivated chain: the access context decides.
#guard aliasBindingCellKey (keyedAlias (.localCapturedAncestorParams ["p"]) none) (accessCtx 1) twoContexts
  == aliasBindingCellKey (keyedAlias (.localCapturedAncestorParams ["p"]) none) (accessCtx 1) EvalState.empty
#guard aliasBindingCellKey (keyedAlias (.localCapturedAncestorParams ["p"]) none) (accessCtx 1) twoContexts
  != aliasBindingCellKey (keyedAlias (.localCapturedAncestorParams ["p"]) none) (accessCtx 2) twoContexts

-- A shared property list under two distinct declaring OWNERS is two bindings, as in the property
-- cache. Erasing the owner's declaration would merge these exported cells (C# shared-DAG regression).
def keyedOwner (declaration : Nat) : ScopeCtx :=
  .mk none ["p"] [] [keyedProp .exported] [] [] none (some (.shared declaration))

#guard aliasBindingCellKey ((keyedAlias .exported none).withParent (some (keyedOwner 20))) (accessCtx 1) twoContexts
  != aliasBindingCellKey ((keyedAlias .exported none).withParent (some (keyedOwner 21))) (accessCtx 1) twoContexts

end KatLang.RuntimeAliasGuards
