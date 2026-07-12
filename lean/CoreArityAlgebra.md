# CoreArityAlgebra — extracted arity algebra (paper artifact)

`CoreArityAlgebra.lean` is a small, self-contained Lean 4 model that isolates
KatLang's **arity** core for a scientific paper. `CoreArityAlgebraProofs.lean`
imports those definitions and proves the small laws and executable checks. These
files are an *extraction* from the authoritative model in
[`KatLang.lean`](./KatLang.lean), not a replacement: the definitions file does
**not** `import KatLang`, so it cannot affect the real model, and it omits
everything that is not about arity (parser, evaluator, arithmetic, properties,
implicit parameters, loops, builtins, strings, and unrelated error modes).

## The one idea

Every arity feature is expressed with a **single recursive carrier**, the
*sequence value* `Val.seq`:

```lean
inductive Val
  | atom : Int → Val
  | seq  : List Val → Val      -- the sequence value: one value, grouped arity
abbrev Supply := List Val      -- many slots (the ungrouped, multi-output context)
```

* `Supply` is *many slots* (output slots / supplied argument slots).
* `Val.seq` is *one value* that groups arity structure.

The operators just move between these two worlds:

| role                                    | operator                         |
| --------------------------------------- | -------------------------------- |
| many slots → one sequence value         | `Val.seq : Supply → Val` (the raw constructor) |
| partial projection of a sequence value's stored items | `sequenceItems? : Val → Option Supply` |
| the total `...` view (`toItems`)        | `items  : Val → Supply`          |
| recursively collapse singleton groups   | `normalize : Val → Val`          |
| rest / variadic capture                 | `capture : Supply → Val`         |
| deconstruction-specific lone-sequence opening of a supply | `openLoneSequence : Supply → Supply` |
| front / rest / back binding kernel      | `bindPats : List Pat → Supply → Option Env` |
| function-call parameter binding         | `bindArgs : List Pat → Supply → Option Env` |
| assignment deconstruction binding (opens a lone sequence) | `bindDeconstruct : List Pat → Supply → Option Env` |

Three of these operations look superficially similar but are semantically
distinct, and the paper's terminology keeps them apart:

| Operation          | Domain          | Purpose                                    |
| ------------------ | --------------- | ------------------------------------------ |
| `items`            | value → supply  | total item view underlying surface spread  |
| `normalize`        | value → value   | persistent-value canonicalization          |
| `openLoneSequence` | supply → supply | deconstruction-specific supply preparation |

`items` is total and models the written spread operator `...`; `normalize`
canonicalizes one stored value by erasing redundant singleton boundaries
recursively; `openLoneSequence` opens a supply consisting of exactly one
sequence value and leaves every other supply unchanged, without recursing
into values.

The headline laws in `CoreArityAlgebraProofs.lean` (all proved, no `sorry`):

* `sequenceItems? (Val.seq xs) = some xs` — the structural projection undoes raw sequence construction; `Val.seq` is a section of `sequenceItems?`.
* `items (Val.seq xs) = xs` — the total view undoes it as well.
* `normalize (Val.seq [Val.seq []]) = Val.seq []` — redundant unary empty structure canonicalizes to `()`.
* `(1,(2,3)) ≠ ((1,2),3)` — nesting matters; a flat item list could not see this.
* rest / variadic capture use `capture xs = normalize (Val.seq xs)` — no second
  collection kind is introduced. (`capture` is *not* the raw constructor: it canonicalizes, so
  `sequenceItems? (capture [1]) = none` while `sequenceItems? (Val.seq [1]) = some [1]`.)

`Val.seq` is deliberately the *raw* constructor: the algebra needs it to state
section laws such as `sequenceItems? (Val.seq xs) = some xs` and to model
pre-normalization structure. Observable KatLang values, by contrast, are
**canonical**: every construction/capture boundary that stores or returns a
newly built sequence value goes through `capture` / `normalize`. In the full
model, capture and written-construction sites apply the deep `Result.normalize`,
while output/collection boundaries combine with the *shallow* singleton-erasing
`combineOutputSlots` / `combineCollectionResult`; the two agree because the
combined items are themselves already canonical (item internals are never
renormalized). A literal-unwritable singleton orphan such as a stored `(5)` is
therefore never observable. Equality stays ordinary structural equality over
those canonical values; comparison does not normalize its operands.

## Why KatLang needs no Python-style `*rest` list

Python's `*rest` binds to a fresh `list`, a container type distinct from the
tuples / iterables it unpacks. That is a reasonable design for *arbitrary iterable*
unpacking. KatLang's arity, by contrast, is centralized around a single structure,
`Sequence`, with canonicalization. Both rest binding (`first, mid..., last = …`)
and variadic capture (`F(x...) = …`) collect captured slots using `Val.seq` and then
normalize the result:

```lean
def capture (xs : Supply) : Val := normalize (Val.seq xs)
```

This introduces **no second collection kind**: capture stays in the sequence world
rather than producing a separate list-like container. The one subtlety is the
`normalize` canonicalization — empty capture stays the empty sequence value,
multi-item capture stays a sequence value, and a *singleton* capture collapses to
the captured value (so `capture [1] = 1`, an atom, not `(1)`). Hence `capture` is
`normalize ∘ Val.seq`, **not** the bare constructor: only `Val.seq` is the exact section of `sequenceItems?`
(`sequenceItems? (Val.seq [1]) = some [1]`, whereas `sequenceItems? (capture [1]) = none`). KatLang
avoids a separate list-like rest container because its arity is sequence-based and
canonicalized — not because capture is the bare sequence constructor.

The Lean algebra permits a lone rest binding as the abstract variadic case:
`bindArgs [Pat.rest "x"] xs` corresponds to variadic capture. KatLang surface
assignment separately rejects rest-only assignment targets such as
`all... = 1, 2, 3`, so this abstract binder is reached through variadic parameter
binding rather than through rest-only assignment syntax.

## Faithfulness

Every behaviour encoded as a theorem was cross-checked against the real evaluator
in `KatLang.lean`, including the subtle points:

* `capture` applies `Result.normalize`, so a rest/variadic that captures exactly
  one item **collapses** to that bare item (`H(x, rest...) = rest` on `H(1,2)`
  gives `rest = 2`), while the empty capture is the empty sequence value
  (`H(1)` gives `rest = ()`), and two-or-more items stay grouped.
* `bindArgs` consumes the call's item supply exactly as supplied: `F(A)` is one
  argument, while `F(A...)` explicitly opens `A` before binding. So a single stored
  sequence value against fixed parameters is an arity error (`Add(A)` fails).
* `bindDeconstruct` is `bindPats ∘ openLoneSequence`: assignment deconstruction is an
  unpacking receiver, so a single sequence-valued right-hand side is
  opened and matched element-by-element. `x, y, z = A` splits `A`, and `x, y, z = A...`
  supplies the same items. This opening is deconstruction-specific — `bindArgs`
  (function calls) does not open — so it does **not** leak into calls (`G(A)` keeps
  `A` as one argument). `openLoneSequence` is the shared lone-sequence opening of a
  supply: it is used by `bindDeconstruct` and by sequence-builtin collection binding
  (`count(A)`, whose one grouped value supplies the collection items), but never by
  `bindArgs`.
  (In `KatLang.lean` these are two code paths — builtin item-supply singleton opening
  via `normalizeSingletonBoundaryForItemSupplyOf` and the deconstruction receiver's
  sequence-value parameter pattern — with the same one-boundary opening behaviour;
  the core model unifies them as the single `openLoneSequence`.)

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
