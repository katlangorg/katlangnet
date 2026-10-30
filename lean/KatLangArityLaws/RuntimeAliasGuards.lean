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

/-! ## L-RUN (M4★): a computed target is established ONCE per declaring activation; calls are fresh

`AT4 = Mk4(5).Algorithm` captures `Z4()` (a ZERO-parameter callee: since M4★ a callable target forwards
at every arity, so `AT4()` is a fresh `Z4()`, never D4's terminal property). Every execution of Mk4's
body allocates ONE `terminalCapture` cell, so its count is the number of receiver executions: the
binding cell (and with it the link's one receiver) is established once for the run whatever observes
it first — a call, a bare read, a chain link — and never again (formerly D4 re-evaluated the row for
every later terminal call). -/

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
A's forwarding target is established ONCE in A's declaring activation (one LocalUse activation): every
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

end KatLang.RuntimeAliasGuards
