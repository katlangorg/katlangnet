# KatLang Semantic Constitution: law summary

> **Constitution catch-up — 2026-11-15 (reconciliation with language changes already landed on `main` since 2026-11-10; owner decisions recorded from the record, none made here; ONE new law, SUP-08; VAL-12 retired; no Q, PV or X status change; over `main` @ `9ec6bf3b`):** The law headings and markers follow `constitution.md`. VAL-02, OP-14, SYN-02 and SYN-15 are restated for the one raw single-quoted string spelling (STR-03, 2026-11-11: string interpolation and double-quoted strings were removed; a `"` is `UnsupportedDoubleQuotedString`), VAL-12 is retired, and SUP-08 *(C#-only)* is the new law for declaration-level output spreading (`A(x, y)* = …`; the static form of November 2026, with the owner decisions D1 and D2 of 2026-11-14). RUN-06 keeps its heading; its body now states `MinDecimalPlaces` and `MaxDecimalPlaces` (owner decision 2026-11-12). LOOP-05 now scopes its marker to *(C#-only: non-integral count rejection)*: the repeat driver is Lean-modeled, and the draft's dated note cites the production arm and driver theorems (E-15 task, `20742ba8`). Source tasks and evidence: the draft's note of the same date and `../constitution-catch-up-20261115/`.

> **Constitution marker check — 2026-11-10 (record correction; no rule text change; no owner decision; no Q, PV or X status change; over `main` @ `c48eb6f9`):** VAR-03, DOT-09 and MOD-03 no longer carry *(Open)*, in step with `constitution.md`: audit findings C-1 (DOT-09) and C-2 (MOD-03) were fixed in `a4181877`, and A-2 (VAR-03) was already recorded as resolved (`8a989f33` / `a6350e23`).

> **Q-66 dot funnel — 2026-11-08 (formal-evidence strengthening; DOT-03's *Open* marker removed because the Q-66 dot-funnel item that qualified it is proved; no rule text change; no owner decision; no Q, PV or X status change; uncommitted over `main` @ `b3cf5771`):** DOT-03 no longer carries *(Open Q-66)*; the draft states what Lean proves and under which premises (`lean/KatLangArityLaws/DotFunnel.lean`, `dot_funnel`), in step with `constitution.md`. Q-66 itself stays OPEN for its other items (`open-questions.md`). Evidence: `artifacts/validation/dot-funnel/`.

Derived from the headings of `constitution.md`, which is the one maintained edition. The former rules-only edition is retired: the constitution itself now leads with its rules. The pre-cleanup copy is `../constitution-cleanup-20261106/backup/constitution-summary.md`.


## VAL — Value model: kinds, canonical forms, value boundaries and counts

- **VAL-01** Every value is exactly one of six kinds, and kinds never convert
- **VAL-02** Strings are opaque scalar values with exact equality, produced only by literals, `.string` and the host
- **VAL-03** Sequences are canonical: there is no one-item sequence *(Open Q-50)*
- **VAL-04** `()` is a real value, never an absence and never an identity
- **VAL-05** An output-less algorithm is a container, not a value: "no output" is never the empty value
- **VAL-06** Every value boundary delivers exactly one value
- **VAL-07** Output rows are an item supply, not a value boundary
- **VAL-08** Element count, supplied items and emitted count are distinct measures
- **VAL-09** Values carry no provenance
- **VAL-10** A failure is not a value: a demanded failure ends the run, and nothing in the language can observe or recover from it
- **VAL-11** A numeric datum carries value and representation: equality ignores representation, observers may not *(C#-only)*
- **VAL-12** (retired: string interpolation was removed, STR-03)

## SEQ — Sequences, lists, and selection

- **SEQ-01** A list is a second collection kind whose own boundary is never normalized
- **SEQ-02** A list literal builds exactly one list from its written slots
- **SEQ-03** Collections are opened only by explicit openers, one boundary at a time: the kind-blind openers open both kinds alike, and a structural pattern opens only its own kind
- **SEQ-04** Selection chooses stored values and never opens them
- **SEQ-05** Selection positions are the target's zero-based one-level positions, and a missing position is an error

## SUP — Item supply: slots, spread, and capture

- **SUP-01** A supply is built slot by slot: each non-spread slot supplies exactly one item, each spread slot supplies its spread items
- **SUP-02** Spread opens exactly one boundary of its operand's value; any other value supplies itself
- **SUP-03** Spread-produced items are established items: no receiver ever reopens them
- **SUP-04** Stacked spread is composition through capture, never recursive flattening: `E**` means `(E*)*`
- **SUP-05** A spread is a slot-level construct, not a value: legal only as a whole slot, as a spread operand, or as the fluent receiver *(C#-only)*
- **SUP-06** Capture turns a supply into one canonical value: `()` for no items, the item itself for one, one sequence for several
- **SUP-07** A capture is a value, never an algorithm identity: no callable, no structural members, no open target
- **SUP-08** A declaration's output-spreading marker changes no algorithm: every eligible call that resolves statically to a marked declaration is elaborated as its written-`*` counterpart *(C#-only)*

## CALL — Calls, argument binding, and parameters

- **CALL-01** A call selects one callee identity first and binds against that callee's signature only
- **CALL-02** A user call forms one argument supply before any binding decision: each non-spread slot supplies a suspended computation of the caller, evaluated only if its value is demanded
- **CALL-03** A builtin callee forms its supply like every call; the builtin decides which non-spread slots it demands, and in what order
- **CALL-04** Arity counts supplied items, and a fixed parameter binds its item unchanged in every call form
- **CALL-05** A zero-argument value demand is accepted exactly when an ordinary zero-argument call can bind the callable *(Open Q-46, Q-58, Q-42)*
- **CALL-06** A written argument slot is evaluated at most once, on its first value demand, and that outcome is final for the call; a slot whose value is never demanded is never evaluated
- **PAR-01** A parameter binds on the value channel, the algorithm channel, or both, and owns its name on every channel
- **PAR-02** (retired: merged into RES-07) *(Open Q-42)*
- **PAR-03** A free name that nothing binds becomes an inferred parameter of the outermost inferring level whose own rows use it *(Open Q-42 C#-only)*
- **PAR-04** An explicit parameter list is closed for its own level: nothing is inferred there, and forwarding never adds a parameter to it *(C#-only)*
- **PAR-05** An inferred signature lists the level's own names by first semantic occurrence, followed by the names it forwards *(C#-only)*
- **PAR-06** Grace `~` moves the OWN inferred parameters of the owner whose rows contain it; saturation is never an error *(C#-only)*
- **PAR-07** In a formula, a value-role reference to a callable that requires supplied arguments becomes a call that forwards the parameter bindings its site already sees; automatic forwarding never changes what an existing name refers to *(C#-only)*
- **PAR-08** Inferred signatures are selected jointly before any rewrite: a recursive inference that settles completes, and only a group with no unique grounded settled answer is refused *(C#-only)*

## NEED — Call by need: supplied computations, demand and transport

- **NEED-01** Supply computations in the caller environment
- **NEED-02** One immutable completed VALUE outcome
- **NEED-03** Executed demands determine effects
- **NEED-04** Ordered pattern inspection and shared clause supply *(Open)*
- **NEED-05** Whole-source validation, then runtime demand phases
- **NEED-06** CALLABLE projection and fresh invocation
- **NEED-07** Lazy supply, eager collection VALUE
- **NEED-08** Forwarding transfers supplies
- **NEED-09** Single flight, cycles, cancellation and resources
- **NEED-10** Retained ownership and separate property cache

## REF — Call references: `meta`, `Invoke`, `Arguments`, `Algorithm`

- **CR-1** META is a binder capability
- **CR-2** Written-order, inert capture
- **CR-3** Identity
- **CR-4** The reference value
- **CR-5** `R.Invoke()`
- **CR-6** Run scope
- **CR-7** Plan retention is decided once and is unobservable *(C#-only)*
- **CR-8** The view
- **CR-9** The view's supply
- **CR-10** Count and selection
- **CR-11** The cell-preserving spread
- **CR-12** Boundaries *(Open Q-84)*
- **CR-13** The callee cell
- **CR-14** The `.Algorithm` intrinsic
- **CR-15** The link
- **CR-16** What obtaining and using `R.Algorithm` does (qualified inertia)
- **CR-17** A builtin may declare META parameters

## VAR — Collecting bindings, deconstruction, and forwarding

- **VAR-01** A collecting binding collects exactly its allocated items as one exact list
- **VAR-02** One collector per pattern level; fixed positions bind from both ends first and the collector takes the exact middle *(Open Q-47)*
- **VAR-03** A collecting binding preserves the supplied argument cells: re-spreading a known slice transfers them with their available capabilities, and only reading the collected list demands their values
- **VAR-04** No binder carries supply provenance: binding sees only the supplied items
- **VAR-05** Assignment deconstruction is the explicit unpacking receiver *(Open Q-51 Open Q-84)*
- **VAR-06** Deconstruction declares properties of the enclosing algorithm; its right-hand side is one row of that body, successfully evaluated at most once *(Open Q-70)*
- **FWD-01** Forwarding collected arguments re-spreads the collector's own cells: spread(collect(S)) = S
- **FWD-02** Bare forwarding reuses existing compatible bindings by name, and a written call means what it writes; every synthesized call forwards bindings unchanged and rebuilds each structural pattern as its own kind *(C#-only Open Q-44)*
- **FWD-03** Whole-algorithm transport: an open body whose one row is a bare algorithm reference is a transparent reference when unbraced and a structural forwarding carrier when braced, and neither owns a zero-argument entry
- **FWD-04** A runtime-target alias takes its callable from one binding cell per declaring activation: an identity of any arity is invoked freshly, absence leaves a value view, and a failure stays a failure

## DOT — Dot syntax: member access, the `.string` intrinsic, and extension calls

- **DOT-01** A declared structural member wins; the extension call happens only on a structural miss
- **DOT-02** Structural-first holds at every level of a chain, and navigation evaluates nothing
- **DOT-03** Extension fallback passes the receiver as the ordinary leading argument: `R.F(args)` ≡ `F(R, args)`
- **DOT-04** The fallback callee is resolved by ordinary callable resolution; a missing member on a known receiver falls back like any other
- **DOT-05** In parameter inference a dot edge contributes receiver, then member (only if the fallback may be selected), then arguments; a closed list checks a certain fallback name *(C#-only)*
- **DOT-06** Grace on a dot edge (`a~.t`, `a.~t`) only reorders inferred parameters; it never changes dispatch *(C#-only)*
- **DOT-07** A fluent receiver `R*.F(args)` is exactly the lexical call `F(R*, args)`; a grouped spread `(R*).F` is a capture receiver; a redundant group is erased
- **DOT-08** `.string` is a dot-only, zero-parameter intrinsic, selected on a structural miss
- **DOT-09** A dot expression carries one callable identity in every position: a structural path is its member, everything else is a value

## RES — Name resolution and ownership

- **RES-01** The owner walk: the nearest owning scope that declares a name decides *(Open Q-44)*
- **RES-02** `open` is consulted only after the whole owner walk; an opened name never overrides anything owned
- **RES-03** At the deciding open level one provider selects; two or more providers are an error, never a fall-through
- **RES-04** A name becomes an implicit parameter only when nothing declares it and no open provides it
- **RES-05** A property may not share a name with a parameter of its own or of any enclosing owner
- **RES-06** Builtins are ordinary, shadowable prelude bindings: the resolved identity decides, never the spelling or the argument count *(Open Q-62)*
- **RES-07** A name inside a declaration denotes what its declaration site sees (lexical scoping), never what the caller or opener sees
- **RES-08** Visibility selects; accessibility is checked on the selected member afterwards (K1-08) *(C#-only Open Q-59)*
- **RES-09** One resolution for every layer, position and execution path
- **RES-10** Declaration order within a scope is not observable

## MOD — The `open` declaration, `load`, and modules

- **MOD-01** An algorithm has at most one `open` declaration, written before its properties and output rows, with one comma-separated target list *(C#-only)*
- **MOD-02** An open target names an algorithm, never a value: a name, an argumentless dotted path, a brace block, or a module *(Open Q-58)*
- **MOD-03** Open targets resolve statically: the head through the owner walk and the direct chain, dotted steps through public members, and every written target must resolve
- **MOD-04** An open provider must need no call, and opening it neither activates nor evaluates it *(Open Q-58)*
- **MOD-05** `open` provides exactly the provider's own public members, and only to the opening body and its nested scopes
- **MOD-06** Opened members keep their definition site; inline open targets and every loaded module are rooted at the prelude
- **MOD-07** `load('url')` is a static source directive that splices a separately parsed module as the one prelude-rooted declaration of its canonical URL, and module elaboration transforms nothing else; `open 'url'` is `open load('url')` *(C#-only Open Q-60 Open Q-62)*
- **MOD-08** A module has hygiene of its own: its free names resolve against the module itself and the prelude, never at the load site
- **MOD-09** One module per canonical URL per compiled program: every load and every open of it is the same declaration *(C#-only)*
- **MOD-10** A clause branch that owns a load materializes its modules only when selected, and then means exactly what eager elaboration would have produced *(C#-only)*
- **MOD-11** A module that is not loaded never becomes a value, and a program with a missing module is never evaluated *(C#-only)*

## PROP — Properties: declarations, demand, and one value per binding per owning invocation

- **PROP-01** Each name is bound once per algorithm; a property is never redefined or reassigned
- **PROP-02** A declaration evaluates nothing: a property body runs only when demanded
- **PROP-03** (retired: merged into RES-10)
- **PROP-04** A zero-parameter property is evaluated at most once for each resolved binding in its owning invocation: once per actual call of the owner around it, once per run where no call owns it
- **PROP-05** How a property's value is consumed never causes its body to run again
- **PROP-06** Only property-style reads reuse the entry: an explicit call invokes afresh and never reads or replaces it, a zero-supply call may only establish an empty one, and freshness is local *(Open Q-83 Open)*
- **PROP-07** Cache identity is the resolved binding, never the spelling or the access path
- **PROP-08** Storage follows the declaring binding and its owning invocation: every actual call of an owner has fresh inner bindings, reads in one call share them, and a binding no call owns is one value per run; exposure decides accessibility and detachment, never lifetime *(Open Q-59)*
- **PROP-09** A binding's entry is created only by its outermost evaluation, and only if it succeeds; the entry is final for the run

## BOOLCMP — Booleans, truth, comparison chains, and builtin `if`

- **BOOL-01** `true`/`false` are a scalar kind of their own, written only as reserved literals, with no Boolean-specific structural rules
- **BOOL-02** Only a Boolean has a truth value *(Open Q-54)*
- **BOOL-03** A Boolean is never a number: no numeric projection, no implicit conversion
- **BOOL-04** `and`/`or`/`xor`/`not` are strict Boolean operators: both operands are evaluated, left to right, before either is validated; there is no short circuit *(Open Q-57)*
- **BOOL-05** Builtin `if` demands its Boolean condition first, then exactly the selected branch; the unselected branch is never demanded
- **CMP-01** The six comparison operators form one chain of adjacent links; a chain is one Boolean, `true` iff every link holds; parentheses end a chain
- **CMP-02** A chain evaluates every operand exactly once, left to right and incrementally; a `false` link never stops it; the first error does
- **CMP-03** `==` and `!=` are total, kind-exact structural equality over every value
- **CMP-04** Ordering (`<`, `>`, `<=`, `>=`) is defined only between numeric scalars
- **CMP-05** On the Decimal128 runtime tier, numeric equality is value equality — representation is not part of it — while ordering is IEEE *(Open Q-56 C#-only)*

## OP — Operators and numerics

- **OP-01** Operators group by one fixed precedence ladder; `^` is right-associative and binds tighter than prefix minus *(Open Q-57 C#-only)*
- **OP-02** Prefix `not` sits between the logical operators and the comparisons, and is never silently regrouped *(C#-only)*
- **OP-03** An operator evaluates its operands in source order, then validates, then applies; the first error ends evaluation
- **OP-04** Arithmetic operators and Math functions take numeric scalars only: no vectorization, no identity element, no concatenation, no coercion
- **OP-05** A number is a 34-digit decimal floating-point value, and every arithmetic result is rounded once *(C#-only)*
- **OP-06** Division, `div` and `mod` by an evaluated zero-valued divisor is an error, never an IEEE infinity or NaN
- **OP-07** A violation of a numeric domain yields an IEEE value, not an error; IEEE special values are ordinary numbers *(C#-only)*
- **OP-08** `div` truncates the exact quotient toward zero, and `mod` is the matching remainder
- **OP-09** `^`, `pow` and `Math.Pow` are one operation; a zero base with any negative exponent is an error
- **OP-10** A numeric literal denotes the nearest Decimal128 value with its written quantum; an out-of-range magnitude is a front-end error *(Open Q-56 C#-only)*
- **OP-11** Every spelling of a Math member is the same function; the spellings are nevertheless distinct bindings *(C#-only)*
- **OP-12** `avg` is the correctly rounded exact mean, independent of element order *(C#-only)*
- **OP-13** `min`/`max` are IEEE minimum/maximum: they return an input element, propagate NaN, and order the two zeros by sign *(Open Q-56 C#-only)*
- **OP-14** `.string` renders a number as its canonical positional text; quantum, sign and specials are part of that string value *(C#-only)*

## ALGHO — Algorithms and the higher-order channel

- **ALG-01** A brace block is a scope-owning algorithm in every expression position
- **ALG-02** Algorithms are not values: only naming forms reach the algorithm channel, and no value is ever callable
- **ALG-03** (retired: merged into SUP-07)
- **ALG-04** (retired: merged into SYN-06) *(C#-only)*
- **ALG-05** Trailing-brace call: `F{…}` is exactly `F({…})` *(C#-only)*
- **ALG-06** (retired: merged into DOT-09)
- **ALG-07** Callable identity is the written declaration plus its captured activation
- **ALG-08** (retired: merged into RES-07)
- **ALG-09** (retired: merged into VAL-05)
- **ALG-10** Consumer-directed observation: a name resolves to one binding, and its consumer decides what to observe
- **HO-01** A callable passed by name is the same callable at the receiver
- **HO-02** The callback law: each element is one ordinary argument, and each callback call is the ordinary call
- **HO-03** A callback returns its ordinary call result: `map` stores it as one element, `reduce` passes it as the next accumulator; `filter` needs a Boolean
- **HO-04** Forwarding preserves the algorithm channel: invoking slots call the named callable, value slots read its value
- **HO-05** Recursion is by name, and every call is a fresh activation whose parameters shadow inherited bindings

## COLL — Collection builtins: one collection argument, one-level view, exact-list results

- **COLL-01** Each builtin has exactly one signature and one behavior contract; none is overloaded by the kind of its input
- **COLL-02** A collection builtin binds exactly one `collection` argument plus fixed controls; argument boundaries are never altered before binding
- **COLL-03** The bound collection is read through ONE post-binding level; `count` counts exactly those items
- **COLL-04** Collection-producing builtins return ONE exact list whose kind never depends on the input; observers return one scalar
- **COLL-05** Numeric collection builtins accept only single numbers; the empty-collection policy is fixed per builtin
- **COLL-06** Aggregates and sorts are defined over the viewed numbers: `order` is a stable ascending sort in which equal numbers tie, and `orderDesc` is its exact reverse *(Open Q-28)*
- **COLL-07** `distinct` and `contains` use the one structural equality of `==`, at the top level of the view
- **COLL-08** `take`/`skip` split the view at a whole-number count and saturate at both ends
- **COLL-09** `range(start, stop)` is the inclusive run of integers in either direction, as one exact list
- **COLL-10** `atoms` is the only recursive flattener and always returns one exact list of numbers

## PAT — Clause families and parameter patterns

- **PAT-01** A same-name clause group is classified as a whole: one literal-free binder/group clause is an ordinary algorithm, anything else is a clause family *(Open Q-46)*
- **PAT-02** A family call selects the first matching clause in written order; no match is NoMatchingBranch *(Open Q-49)*
- **PAT-03** A family has one outer call interface: every clause takes the same number of argument slots and writes the same number of output rows *(Open Q-48)*
- **PAT-04** A clause head is the complete input specification of its branch *(Open Q-47)*
- **PAT-05** A literal pattern matches only an equal value of its own kind
- **PAT-06** Structural pattern delimiters select the value kind they destructure: a parenthesized pattern matches sequence values only, a bracketed pattern list values only, and a one-item sequence pattern is invalid
- **PAT-07** A clause family demands only what its patterns inspect, and its binders keep both channels of their cells
- **PAT-08** An ordinary structural parameter pattern consumes one argument and opens that argument's value exactly one level, through its own kind
- **PAT-09** A repeated name is a compatibility constraint over independently supplied arguments, never a merge or a rebinding *(Open)*
- **PAT-10** A pattern list is inspected in written order after its cardinality check, and the first failure or conflict that inspection meets is reported
- **PAT-11** A clause family is an ordinary callable: it can be passed, called back and dot-called, its call result is one value, and a zero-argument value demand of it is NoMatchingBranch

## LOOP — `repeat` and `while`: stepping an explicit multi-slot state

- **LOOP-01** The initial state is one state slot per supplied argument of the captured step call
- **LOOP-02** Each iteration invokes the step on the current state as the ordinary call
- **LOOP-03** The step's emitted row supply becomes the next state; patterns bind, they never produce
- **LOOP-04** (retired: merged into LOOP-03) *(C#-only)*
- **LOOP-05** `repeat` invokes the step exactly `count` times, and `count` is a non-negative whole number *(C#-only: non-integral count rejection)*
- **LOOP-06** `while` reads its continuation flag first: the last effective output item is a Boolean flag, and `false` returns the state that entered the round
- **LOOP-07** The loop result is ONE value: the canonical capture of the final state's slots, one item at every receiver
- **LOOP-08** A loop step is an ordinary callable invoked over the current state supply *(Open Q-39)*

## SYN — Syntax and layout: vocabulary, rows, delimiters, separators, lines, and markers

- **SYN-01** Exactly ten words are reserved; every other identifier-shaped word is an ordinary name, and names are exact *(C#-only)*
- **SYN-02** Literal forms: unsigned decimal numbers, raw single-quoted strings, and the two Boolean keywords *(C#-only)*
- **SYN-03** `#` comments are invisible to the grammar, and a physical line ends only at a line feed *(C#-only)*
- **SYN-04** An algorithm body is a set of declarations plus an ordered list of output rows; there is no output keyword
- **SYN-05** Only a brace block (and the root) creates a scope; parentheses group and capture, brackets build lists, and indentation means nothing
- **SYN-06** Parentheses group syntax: a one-slot, non-spread group IS its content, so `E ≡ (E) ≡ ((E))` everywhere *(C#-only)*
- **SYN-07** On one physical line only a comma separates slots; a newline separates slots only where a list is open across lines; `;` is not KatLang syntax *(C#-only)*
- **SYN-08** Grammar role has priority across physical newlines *(C#-only)*
- **SYN-09** A call is written only as a same-line `(` or `{` after a callable name or argumentless dot edge; juxtaposition never calls and never multiplies *(C#-only Open Q-46)*
- **SYN-10** Declarations are line-anchored: each begins a line, its head never spans lines, and a head is never an operand *(C#-only)*
- **SYN-11** Star roles are syntactic; a line-final star is classified by attachment *(C#-only)*
- **SYN-12** Markers and special prefix roles require attachment; binary operators retain ordinary spacing *(C#-only)*
- **SYN-13** The grammar never consults meaning: no parse depends on arity, values, types, name resolution, or callee spelling, except MOD-07's `load(...)` open-target form check *(C#-only)*
- **SYN-14** Recovery is not grammar: recovery trees, stand-ins, delimiter repairs and clause-head confinement give malformed text no meaning *(C#-only)*
- **SYN-15** A string has one spelling, raw single-quoted text; a double quote is the targeted front-end error `UnsupportedDoubleQuotedString` *(C#-only)*

## RUN — Runtime transparency, evaluation outcome, host policy, and seeded randomness

- **RUN-01** The meaning of a program is independent of the execution route *(Open Q-41 C#-only)*
- **RUN-02** The run is the unit of evaluation state
- **RUN-03** Runtime protection is host policy: it may stop a run, never redefine it *(Open Q-39 Open Q-40 Open Q-41)*
- **RUN-04** A source with any front-end error is never evaluated, and recovery gives malformed text no meaning *(Open Q-41 C#-only)*
- **RUN-05** Host operations are ordinary prelude members; each executed call invokes the host exactly once *(C#-only)*
- **RUN-06** Presentation is not meaning: display settings change only rendered text *(C#-only)*
- **RUN-07** A run yields its output or exactly one error: errors are not values, cannot be caught, and end the run; the outcome is the first RAISED failure in the evaluation order the rules fix *(Open Q-42)*
- **RUN-08** Evaluation is strict except at a closed set of demand points, and "exactly once" has enumerated exceptions
- **RUN-09** `tick()` counts actual executions: one counter per run, advanced only when the primitive executes
- **RAND-01** One run-scoped random stream, consumed exactly where evaluation executes a random call *(C#-only)*
- **RAND-02** A seed is host configuration: it reproduces the stream, never memoizes, and has no source syntax *(C#-only)*
- **RAND-03** `random`/`randomInt` draw uniformly from a half-open interval, and validation precedes every draw *(C#-only)*

## FORMAL — Lean/C# correspondence: authority, model coverage, and what is proved

- **FORMAL-01** `lean/KatLang.lean` is the normative semantics of every construct it models
- **FORMAL-02** Lean models the elaborated core; surface syntax and front-end elaboration are C#-only, and both sides run the same elaborated program
- **FORMAL-03** Everything outside the Lean model is C#-only by design and must extend the modeled core conservatively *(C#-only)*
- **FORMAL-04** Numerics are two-tier: Lean's `Int` laws bind C# on the common exact integer subdomain, and Decimal128-only behavior has no Lean witness
- **FORMAL-05** Counted evaluation is the one meaning of an expression; plain evaluation is its value projection
- **FORMAL-06** Lean/C# agreement is defined on the neutral observation: structure, emitted count, and innermost error kind
- **FORMAL-07** Proofs cover total helpers and operation-level laws of the fuel-indexed evaluator core; whole-program evaluation is checked executably on bounded corpora
- **FORMAL-08** The constitution is stated over the source-reachable elaborated core; host-built shapes outside it are not constitutional
