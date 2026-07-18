# CoreArityAlgebra — extracted arity algebra (paper artifact)

`CoreArityAlgebra.lean` is a small, self-contained Lean 4 model that isolates
KatLang's **arity** core for a scientific paper. `CoreArityAlgebraProofs.lean`
imports those definitions and proves the small laws and executable checks. These
files are an *extraction* from the authoritative model in
[`KatLang.lean`](./KatLang.lean), not a replacement: the definitions file does
**not** `import KatLang`, so it cannot affect the real model, and it omits
everything that is not about arity (parser, evaluator, arithmetic, properties,
implicit parameters, loops, builtins, strings, and unrelated error modes).

> **Model revision (July 2026).** The original extraction (git tag
> `arity-algebra-2026-07-12`, the version pinned by the paper) was
> sequence-only: rest/variadic binding was `captureVariadic := capture`, so a
> rest canonicalized to a sequence value and a singleton rest collapsed to its
> item. The language has since made **all rest bindings collect exact
> immutable lists**, and this artifact tracks the authoritative model: it now
> carries `Val.list`, the `collect` operation, and distinction theorems in
> place of the old grouped/spread coincidence theorems. Consult the pinned tag
> for the historical model the paper describes.

## The one idea

Arity is expressed with a **single item-supply discipline** over two stored
collection kinds:

```lean
inductive Val
  | atom : Int → Val
  | seq  : List Val → Val      -- the sequence value: one value, grouped arity
  | list : List Val → Val      -- the exact immutable list value: no canonicalization
abbrev Supply := List Val      -- many slots (the ungrouped, multi-output context)
```

* `Supply` is *many slots* (output slots / supplied argument slots).
* `Val.seq` is *one value* that groups arity structure and canonicalizes.
* `Val.list` is *one value* that stores its elements exactly.

Three typed operations move between the two worlds, distinguished by receiver
purpose:

```text
capture : Supply → Value      -- ordinary value/output capture (canonicalizing)
collect : Supply → ListValue  -- rest/variadic binding (exact)
open    : Value → Supply      -- postfix spread `...` (one boundary)
```

| role                                    | operator                         |
| --------------------------------------- | -------------------------------- |
| many slots → one sequence value         | `Val.seq : Supply → Val` (the raw constructor) |
| partial projection of a sequence value's stored items | `sequenceItems? : Val → Option Supply` |
| partial projection of a list value's stored elements | `listItems? : Val → Option Supply` |
| the total `...` view (`open`)           | `items  : Val → Supply`          |
| recursively collapse singleton sequence groups | `normalize : Val → Val`   |
| ordinary value capture                  | `capture : Supply → Val`         |
| rest / variadic collection              | `collect : Supply → Val` (always `Val.list`) |
| deconstruction-specific lone-structure opening of a supply | `openLoneStructure : Supply → Supply` |
| front / rest / back binding kernel      | `bindPats : List Pat → Supply → Option Env` |
| function-call parameter binding         | `bindArgs : List Pat → Supply → Option Env` |
| assignment deconstruction binding (opens a lone structure) | `bindDeconstruct : List Pat → Supply → Option Env` |

Several of these operations look superficially similar but are semantically
distinct, and the paper's terminology keeps them apart:

| Operation           | Domain          | Purpose                                    |
| ------------------- | --------------- | ------------------------------------------ |
| `items`             | value → supply  | total item view underlying surface spread (opens one sequence OR list boundary) |
| `normalize`         | value → value   | persistent-value canonicalization (sequence singletons erase; list boundaries never do) |
| `capture`           | supply → value  | ordinary value capture, `normalize ∘ Val.seq` |
| `collect`           | supply → value  | exact rest collection, always a `Val.list` |
| `openLoneStructure` | supply → supply | deconstruction-specific supply preparation |

The headline laws in `CoreArityAlgebraProofs.lean` (all proved, no `sorry`):

* `sequenceItems? (Val.seq xs) = some xs` and `listItems? (Val.list xs) = some xs`
  — the structural projections undo raw construction.
* `items (Val.seq xs) = xs` and `items (Val.list xs) = xs` — surface spread
  opens exactly one boundary of either collection kind.
* `normalize (Val.seq [Val.seq []]) = Val.seq []` — redundant unary empty
  sequence structure canonicalizes to `()`, while
  `normalize (Val.list xs) = Val.list (normalizeList xs)` — list boundaries
  are exact.
* `(1,(2,3)) ≠ ((1,2),3)` — nesting matters; a flat item list could not see this.
* **Rest collection is exact** (`collect xs = Val.list xs`):
  `collect_is_list` (stable result kind and exact elements), `collect_length`
  (exact length), `collect_singleton` with `collect_singleton_ne_item`
  (singleton preservation — `collect [v] = [v] ≠ v`), `items_collect`
  (the open/collect round trip `open (collect xs) = xs`), and
  `collect_spread_concat_exact` / `collect_congr` (provenance independence —
  the result depends only on the assembled supply).
* **The grouped/spread coincidence is gone**:
  `variadic_collect_distinguishes_spread` proves
  `bindArgs [rest r] [Val.seq ys] ≠ bindArgs [rest r] (items (Val.seq ys))` —
  `Sum(A)` and `Sum(A...)` bind observably different rest values
  (`[A]` vs `[a₁, …, aₙ]`). `receivers_never_agree_on_lone_seq` generalizes
  this: for every pattern list, call binding and deconstruction never produce
  the same successful binding on a lone sequence value (the pre-list model's
  `agree_on_lone_seq_iff_lone_rest` characterized rest-only as the one
  agreeing shape; exact collection removes that coincidence).
  `lone_rest_disagrees_on_lone_list` is the concrete list-side twin.
* `capture (before ++ items (Val.seq []) ++ after) = capture (before ++ after)`
  — the empty spread `()...` contributes zero items to the surrounding supply,
  so it is neutral at the canonical capture boundary
  (`capture_empty_spread_neutral`); the concrete KatLang consequence is
  `(n, ()...) == n` (`capture_atom_empty_spread`).

`Val.seq` is deliberately the *raw* constructor: the algebra needs it to state
section laws such as `sequenceItems? (Val.seq xs) = some xs` and to model
pre-normalization structure. Observable KatLang sequence values, by contrast,
are **canonical**: every construction/capture boundary that stores or returns a
newly built sequence value goes through `capture` / `normalize`. In the full
model, capture and written-construction sites apply the deep `Result.normalize`,
while output boundaries combine with the *shallow* singleton-erasing
`combineOutputSlots`; the two agree because the
combined items are themselves already canonical (item internals are never
renormalized). A literal-unwritable singleton orphan such as a stored `(5)` is
therefore never observable. Exact list values carry no orphan rule at all:
`[x]` is literal-writable, so `orphanFree` checks only their elements.
Equality stays ordinary structural equality; comparison does not normalize its
operands, and a list never equals a sequence value (`list_ne_seq`).

## Rest binding collects an exact list

Python's `*rest` binds to a fresh `list`, a container type distinct from the
tuples / iterables it unpacks. KatLang now makes the same receiver-purpose
distinction, with its own exact collection kind: every rest binding —
deconstruction rest (`first, mid..., last = …`) and variadic parameters
(`F(x...) = …`) — materializes the assigned item supply through `collect`:

```lean
def collect (xs : Supply) : Val := Val.list xs
```

* zero assigned items → `[]` (a visible exact value, not the invisible `()`),
* one assigned item → `[item]` (never erased to the item),
* many assigned items → `[item₁, item₂, …]`.

Ordinary value capture (`x = 1, 2, 3`) still uses the canonicalizing
`capture = normalize ∘ Val.seq` — the two operations coexist and are proven
distinct (`collect_singleton_atom_ne_capture`). The practical payoff of exact
collection is that a rest of one structured item stays distinguishable from
the item's own elements (`first, rest... = Rows` with one remaining row binds
`rest = [[3, 4]]`, count 1 — not the row `[3, 4]` itself), and that variadic
forwarding is ordinary spread: `open (collect xs) = xs` (`items_collect`), so
`Forward(items...) = Target(items...)` re-supplies exactly the collected
items with no hidden raw-supply metadata.

The Lean algebra permits a lone rest binding as the abstract variadic case:
`bindArgs [Pat.rest "x"] xs` corresponds to variadic capture. KatLang surface
assignment separately rejects rest-only assignment targets such as
`all... = 1, 2, 3`, so this abstract binder is reached through variadic parameter
binding rather than through rest-only assignment syntax.

## Faithfulness

Every behaviour encoded as a theorem was cross-checked against the real evaluator
in `KatLang.lean`, including the subtle points:

* `collect` is exact: a rest/variadic that captures exactly one item binds the
  one-element list (`H(x, rest...) = rest` on `H(1, 2)` gives `rest = [2]`),
  the empty capture is the empty list (`H(1)` gives `rest = []`), and
  two-or-more items stay `[…]`. In `KatLang.lean` the shared helper is
  `collectRest`; in the C# runtime it is `CollectRest` inside
  `CreateVariadicCapture`.
* `bindArgs` consumes the call's item supply exactly as supplied: `F(A)` is one
  argument, while `F(A...)` explicitly opens `A` before binding. So a single stored
  sequence or list value against fixed parameters is an arity error (`Add(A)`
  fails), and a rest-only call distinguishes `F(A)` (`rest = [A]`) from
  `F(A...)` (`rest = [a₁, …]`).
* `bindDeconstruct` is `bindPats ∘ openLoneStructure`: assignment deconstruction is an
  unpacking receiver, so a single sequence- or list-valued right-hand side is
  opened and matched element-by-element. `x, y, z = A` splits `A`, and `x, y, z = A...`
  supplies the same items. This opening is deconstruction-specific — `bindArgs`
  (function calls) does not open — so it does **not** leak into calls (`G(A)` keeps
  `A` as one argument). `openLoneStructure` is the shared lone-structure opening of a
  received value: it is used by `bindDeconstruct` and by the collection builtins'
  POST-BINDING collection view (`count(A)`, whose already-bound collection argument
  supplies the collection items), but never by `bindArgs`.
  (In `KatLang.lean` these are two code paths — the post-binding builtin collection
  view `builtinCollectionItems`, applied to the bound `collection` argument of an
  ordinary fixed-arity builtin call, and the deconstruction receiver's
  sequence-value parameter pattern via `Result.structureItems?` — with the same
  one-boundary opening behaviour; the core model unifies them as the single
  `openLoneStructure`.)
* After the receiver-specific supply preparation, call and deconstruction rest
  bindings share the SAME collection rule: both are `bindPats`, whose single
  rest case materializes through `collect` (`bindArgs = bindPats`,
  `bindDeconstruct = bindPats ∘ openLoneStructure` — definitional in
  `CoreArityAlgebra.lean`).

See the provenance table in the file header for the exact `KatLang.lean`
correspondences.

## Build / validate

The definitions and checks are wired as isolated Lean library targets in
[`lakefile.lean`](./lakefile.lean):

```powershell
# from the lean/ directory
lake build CoreArityAlgebra
lake build CoreArityAlgebraProofs
```

It is also included in the repo-wide validation script:

```powershell
# from repo root
pwsh .\scripts\validate-all.ps1
```

The proof file contains no `sorry`, `admit`, `axiom`, or `native_decide`: every
check is closed by elementary tactics (`rfl`, `decide`, `simp`, `omega`, and
small structured case analyses).
