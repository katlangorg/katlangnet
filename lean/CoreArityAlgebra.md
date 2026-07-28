# CoreArityAlgebra — extracted arity algebra (paper artifact)

`CoreArityAlgebra.lean` is a small, self-contained Lean 4 model that isolates
KatLang's **arity** core for a scientific paper. `CoreArityAlgebraProofs.lean`
imports those definitions and proves the small laws and executable checks. These
files are an *extraction* from the authoritative model in
[`KatLang.lean`](./KatLang.lean), not a replacement: the definitions file does
**not** `import KatLang`, so it cannot affect the real model, and it omits
everything that is not about arity (parser, evaluator, arithmetic, properties,
implicit parameters, loops, builtins, strings, and unrelated error modes).

> **History.** The original extraction (git tag `arity-algebra-2026-07-13`, the
> version pinned by the paper) was sequence-only: collecting bindings went through
> `captureVariadic := capture`, so a collected segment canonicalized to a sequence value and
> a singleton collected segment collapsed to its item. The language has since made **all
> collecting bindings collect exact immutable lists**, and this artifact tracks the
> stabilized current model described below. Consult the pinned tag for the
> historical model the current paper text describes.

## The one idea

KatLang arity uses **one temporary item-supply discipline and two
receiver-purpose materializations**. `capture` reifies a supply as a canonical
stored value, `collect` preserves it as an exact immutable list for collecting
bindings, and `spread` exposes one stored boundary as a supply:

```text
capture : Supply → Value      -- ordinary value/output capture (canonicalizing)
collect : Supply → ListValue  -- collecting binding (exact)
spread  : Value → Supply      -- the spread intrinsic `spread(e)` / `e.spread` (one boundary)
```

The responsibilities never mix: ordinary value/output boundaries go through
`capture`, collecting bindings go through `collect`, and the spread intrinsic is `spread`.
Grouping preserves one value boundary, spread opens one boundary, and a collecting binding
collects the resulting slots into an exact immutable list.

`collect : Supply → ListValue` is the *conceptual* typed signature; executable
Lean gives `collect` the codomain `Val` and always constructs the result with
the `Val.list` constructor, with the refined result kind established by
theorem (`collect_is_list`) rather than by a separate top-level `ListValue`
type.

The value model carries two stored collection kinds over one supply type:

```lean
inductive Val
  | atom : Int → Val
  | seq  : List Val → Val      -- the sequence value: one value, grouped arity
  | list : List Val → Val      -- the exact immutable list value: no canonicalization
abbrev Supply := List Val      -- many slots (the ungrouped, multi-output context)
```

* `Supply` is *many slots* (output slots / supplied argument slots).
* `Val.seq` is the raw *one value* constructor that groups arity structure;
  `capture` / `normalize` perform canonicalization at ordinary value boundaries.
* `Val.list` is *one value* that stores its elements exactly.

| role                                    | operator                         |
| --------------------------------------- | -------------------------------- |
| many slots → one sequence value         | `Val.seq : Supply → Val` (the raw constructor) |
| partial projection of a sequence value's stored items | `sequenceItems? : Val → Option Supply` |
| partial projection of a list value's stored elements | `listItems? : Val → Option Supply` |
| shared openable-structure projection    | `structureItems? : Val → Option Supply` |
| the total named-spread view               | `items  : Val → Supply`          |
| recursively collapse singleton sequence groups | `normalize : Val → Val`   |
| ordinary value capture                  | `capture : Supply → Val`         |
| the canonical-supply invariant          | `canonicalSupply : Supply → Prop` |
| collecting-binding collection              | `collect : Supply → Val` (always `Val.list`) |
| deconstruction-specific lone-structure opening of a supply | `openLoneStructure : Supply → Supply` |
| the one supply shape that opening rewrites | `loneStructure : Supply → Bool` |
| front / collecting / back binding kernel      | `bindPats : List Pat → Supply → Option Env` |
| function-call parameter binding         | `bindArgs : List Pat → Supply → Option Env` |
| assignment deconstruction binding (opens a lone structure) | `bindDeconstruct : List Pat → Supply → Option Env` |

Several of these operations look superficially similar but are semantically
distinct, and the paper's terminology keeps them apart:

| Operation           | Domain          | Purpose                                    |
| ------------------- | --------------- | ------------------------------------------ |
| `structureItems?`   | value → supply? | openable-structure view (sequence OR list opens; atoms do not) |
| `items`             | value → supply  | total item view underlying surface spread (`structureItems?` with a one-item scalar fallback — `structureItems?_getD_eq_items`) |
| `normalize`         | value → value   | persistent-value canonicalization (sequence singletons erase; list boundaries never do) |
| `capture`           | supply → value  | ordinary value capture, `normalize ∘ Val.seq` |
| `collect`           | supply → value  | exact segment collection, always a `Val.list` |
| `openLoneStructure` | supply → supply | deconstruction-specific supply preparation |

## The receiver split

The two binding receivers are the same front/collecting/back kernel (`bindPats`)
with different supply preparation:

```lean
def bindArgs        (ps : List Pat) (xs : Supply) := bindPats ps xs
def bindDeconstruct (ps : List Pat) (xs : Supply) := bindPats ps (openLoneStructure xs)
```

Calls preserve the supplied argument slots; assignment deconstruction may
first open ONE lone sequence or lone list (`loneStructure` characterizes
exactly that supply shape). The receiver theorems split the whole story on
that predicate:

* `receivers_agree_outside_lone_structure` — with `loneStructure xs = false`
  the receivers are equal, so the entire asymmetry lives in the
  lone-structure case;
* `deconstruct_singleton_eq_args_items` — on a single-value supply the
  deconstruction receiver binds exactly what the call receiver binds on the
  value's immediate item view;
* `receivers_never_same_on_lone_structure` — on a lone structure
  (`[Val.seq ys]` and `[Val.list ys]` alike) the receivers NEVER both succeed
  with the same environment, for any pattern list. Per-kind corollaries:
  `receivers_never_agree_on_lone_seq`, `receivers_never_agree_on_lone_list`.
  Shared *success* is the strongest correct claim — both receivers can fail
  identically (two fixed names vs a one-item payload), so plain Option
  inequality would be false. The pre-list characterization
  `agree_on_lone_seq_iff_lone_rest` (lone-collecting agreement via the
  canonical-capture coincidence) is obsolete: exact collection distinguishes
  the grouped argument (`rest = [A]`) from the spread items;
* `lone_collecting_disagrees_on_lone_list` — a concrete lone-collecting disagreement
  where both modes DO succeed, so even the Option values differ.

The item-view equation is deliberately receiver-level. It is not an
unrestricted source rewrite from `x, y = A` to `x, y = A.spread`, because a
written assignment RHS is captured into one shared value before the
deconstruction receiver runs. For the minimal boundary-sensitive case
`A = [(1, 2)]`, bare `x, y = A` opens the list once and still sees one row, so
it fails arity; `x, y = A.spread` spreads that row into the capture boundary,
whose singleton normalization returns `(1, 2)`, and the receiver then opens
the row and succeeds. `deconstruct_spread_capture_can_open_further` pins this
counterexample in the extraction, while `CoreTests.lean` and
`CollectingBindingTests.cs` pin the authoritative Lean/C# surface behavior.

`openLoneStructure` models a common one-boundary transformation applied after
a receiver has selected one structured value: in the full model it appears as
the deconstruction receiver's opening (`(Result.structureItems? value).getD
[value]` inside the sequence-value parameter pattern binder) and, with the
same one-boundary behaviour, as the collection builtins' POST-BINDING view of
the bound `collection` argument (`builtinCollectionItems`). The extraction
unifies the two as one operation; that does **not** mean assignment
deconstruction and collection builtins share one runtime call path.

## Round-trip laws

The three operations compose as partial inverses, each on its own documented
domain:

```text
spread ∘ collect = id  on supplies                    (items_collect)
collect ∘ spread = id  on exact list values           (collect_items_list)
capture ∘ spread = id  on canonical non-list values   (capture_items_of_canonical)
```

The `capture` restriction is real: spreading a list and re-CAPTURING converts
it to the sequence world (`capture_items_of_list` — `x = A.spread` with
`A = [1, 2, 3]` gives `(1, 2, 3)`), so the unrestricted claim would be false.
The first law is what makes variadic forwarding ordinary list spread:
`Forward(items...) = Target(items.spread)` re-supplies exactly the collected
items with no hidden raw-supply metadata.

## Collecting binding collects an exact list

Python's `*rest` binds to a fresh `list`, a container type distinct from the
tuples / iterables it unpacks. KatLang makes the same receiver-purpose
distinction, with its own exact collection kind: every collecting binding —
deconstruction collecting bindings (`first, mid..., last = …`) and variadic parameters
(`F(x...) = …`) — materializes the assigned item supply through `collect`:

```lean
def collect (xs : Supply) : Val := Val.list xs
```

* zero assigned items → `[]` (a visible exact value, not the invisible `()`),
* one assigned item → `[item]` (never erased to the item),
* many assigned items → `[item₁, item₂, …]`.

`collect` deliberately does **not** normalize or flatten its input: it
preserves the exact number, order, value kinds, and boundaries of the
supplied values. Canonicality of the collected list is an *invariant of the
input* (`canonicalSupply`, below), not extra work inside `collect`.

The headline exactness laws in `CoreArityAlgebraProofs.lean`:

* `collect_is_list` — stable result kind and exact elements;
* `collect_length` — exact length;
* `collect_singleton` / `collect_singleton_seq` / `collect_singleton_list`
  with `collect_singleton_ne_item` — singleton preservation for EVERY value
  kind (`collect [v] = [v] ≠ v`), which keeps one remaining structured row
  distinct from the row's own elements (`first, rest... = 1, (2, 3)` binds
  `rest = [(2, 3)]`; `1, [2, 3]` binds `[[2, 3]]`; `1, ()` binds `[()]`;
  `1, []` binds `[[]]`);
* `items_collect` — the open/collect round trip;
* `collect_spread_concat_exact` / `collect_congr` — provenance independence:
  the result depends only on the assembled supply, never on which source
  structures were spread to produce it.

**The generic binding law.** `bindPats_collecting_split` and `bindPats_collect_exact`
establish segment collection for every single-variadic parameter list at once: for
collecting-free `front`/`back` and any supply `frontVals ++ mid ++ backVals` with
matching fixed lengths,

```lean
bindPats (front ++ Pat.collecting r :: back) (frontVals ++ mid ++ backVals)
  = some (bindFixed front frontVals ++ (r, collect mid) :: bindFixed back backVals)
```

— the fixed captures bind positionally from the front and the back, and the
single movable collecting binding collects exactly the middle supply, for empty, singleton,
and multiple middles and for leading/middle/trailing positions
(`bindPats_leading_collecting`, `bindPats_middle_collecting`, `bindPats_trailing_collecting`,
`bindPats_lone_collecting` are the shape instances). The environment is stated
structurally, so no name-uniqueness premise is needed; surface KatLang
rejects duplicate parameter names before this binder model is reached, and
the full model's binder additionally merges duplicate bindings with an
equality check that the extraction omits.

The Lean algebra permits a lone collecting binding:
`bindArgs [Pat.collecting "x"] xs` is the single variadic parameter
`F(items...)`, and the lone-collecting assignment `all... = 1, 2, 3` reaches
the same shape through the deconstruction receiver (`bindDeconstruct`),
collecting the complete supply as one exact list.

## Canonical values and the canonical-supply invariant

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
therefore never observable (`normalize_idempotent`, `orphanFree_normalize`,
`capture_canonical`, `capture_orphanFree`). Exact list values carry no orphan
rule at all: `[x]` is literal-writable, so `orphanFree` checks only their
elements. Equality stays ordinary structural equality; comparison does not
normalize its operands, and a list never equals a sequence value
(`list_ne_seq`).

The supply-level face of the same story is `canonicalSupply`
(`normalizeList xs = xs`, equivalently every member is a `normalize` fixed
point — `canonicalSupply_iff_forall`): the abstract `Supply` type admits raw
non-canonical members, but observable runtime supplies are canonical, and the
invariant is closed under the algebra's operations:

* `canonicalSupply_normalizeList` — normalization produces canonical supplies;
* `canonicalSupply_items_of_canonical` — opening a canonical value yields a
  canonical supply (`open` preserves the invariant);
* `normalize_collect_of_canonicalSupply` — collecting a canonical supply is
  already canonical, with `collect_orphanFree_of_elements` as the
  orphan-freedom face and `normalize_collect_items_of_canonical` as the
  end-to-end composition. This is the precise sense in which `collect` needs
  no normalization of its own — and the full model's `collectSegment` / the C#
  `CollectSegment` likewise store their supply unchanged.

## Zero-item spreads are neutral

`()` and `[]` are exactly the values whose spread contributes no items
(`items_eq_nil_iff`), and both materialization boundaries ignore such an
open wherever it is inserted:

* generic: `capture_zero_item_spread_neutral`, `collect_zero_item_spread_neutral`
  (over any `items v = []`);
* sequence instances: `capture_empty_spread_neutral`,
  `capture_atom_empty_spread` (`(n, ().spread) == n`);
* list instances: `capture_empty_list_spread_neutral`,
  `capture_atom_empty_list_spread` (`(n, [].spread) == n`).

The unspread values stay visible one-item slots (`E(())` collects `[()]`,
`E([])` collects `[[]]`), while their spreads vanish (`E(().spread)` and
`E([].spread)` collect `[]`) — neutrality is a property of the *spread* supply,
never of the value itself.

## Faithfulness

Every behaviour encoded as a theorem was cross-checked against the real evaluator
in `KatLang.lean`, including the subtle points:

* `collect` is exact: a variadic parameter that collects exactly one item binds the
  one-element list (`H(x, rest...) = rest` on `H(1, 2)` gives `rest = [2]`),
  the empty segment is the empty list (`H(1)` gives `rest = []`), and
  two-or-more items stay `[…]`. In `KatLang.lean` the shared helper is
  `collectSegment`; in the C# runtime it is `CollectSegment` inside
  `CreateVariadicCapture`.
* `bindArgs` consumes the call's item supply exactly as supplied: `F(A)` is one
  argument, while `F(A.spread)` explicitly spreads `A` before binding. So a single stored
  sequence or list value against fixed parameters is an arity error (`Add(A)`
  fails), and a single-variadic call distinguishes `F(A)` (`rest = [A]`) from
  `F(A.spread)` (`rest = [a₁, …]`).
* `bindDeconstruct` is `bindPats ∘ openLoneStructure`: assignment
  deconstruction is an unpacking receiver, so a single sequence- or
  list-valued right-hand side is opened and matched element-by-element.
  Receiver-level opening is exactly one boundary. A written RHS spread first
  passes through the ordinary shared-value capture boundary, so the surface
  bare/spread forms can differ on a singleton structured element as described
  above; the extraction does not hide that lower capture-boundary detail.
  This opening is deconstruction-specific — `bindArgs` (function calls) does
  not open — so it does **not** leak into calls (`G(A)` keeps `A` as one
  argument).
* After the receiver-specific supply preparation, call and deconstruction collecting
  bindings share the SAME collection rule: both are `bindPats`, whose single
  collecting case materializes through `collect` (`bindArgs = bindPats`,
  `bindDeconstruct = bindPats ∘ openLoneStructure` — definitional in
  `CoreArityAlgebra.lean`).
* `structureItems?` mirrors the authoritative `Result.structureItems?`, and
  `openLoneStructure [v]` is definitionally
  `(structureItems? v).getD [v]` — the exact shape of the full model's
  deconstruction binder
  (`openLoneStructure_single_eq_structureItems?_getD`).

See the provenance table in the file header for the exact `KatLang.lean`
correspondences, and `KatLangArityLaws.lean` for the bridge theorems proved
over the real `Result` model (binder-path collection laws, receiver-contrast
laws for both structure kinds, round trips, and canonicality of collected
lists).

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
