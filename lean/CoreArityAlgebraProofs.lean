/-
Proofs and executable checks for CoreArityAlgebra.

The definitions live in CoreArityAlgebra.lean. This file contains the
small laws, edge-case checks, and binding examples used by the paper and by
reviewers to validate the algebra.
-/

import CoreArityAlgebra

namespace CoreArityAlgebra

mutual
  def Val.decEq : (a b : Val) -> Decidable (a = b)
    | .atom m, .atom n =>
        if h : m = n then .isTrue (by rw [h]) else .isFalse (by intro he; cases he; exact h rfl)
    | .seq xs, .seq ys =>
        match Val.decEqList xs ys with
        | .isTrue h => .isTrue (by rw [h])
        | .isFalse h => .isFalse (by intro he; cases he; exact h rfl)
    | .list xs, .list ys =>
        match Val.decEqList xs ys with
        | .isTrue h => .isTrue (by rw [h])
        | .isFalse h => .isFalse (by intro he; cases he; exact h rfl)
    | .atom _, .seq _ => .isFalse (by intro he; cases he)
    | .atom _, .list _ => .isFalse (by intro he; cases he)
    | .seq _, .atom _ => .isFalse (by intro he; cases he)
    | .seq _, .list _ => .isFalse (by intro he; cases he)
    | .list _, .atom _ => .isFalse (by intro he; cases he)
    | .list _, .seq _ => .isFalse (by intro he; cases he)

  def Val.decEqList : (xs ys : List Val) -> Decidable (xs = ys)
    | [], [] => .isTrue rfl
    | [], _ :: _ => .isFalse (by intro he; cases he)
    | _ :: _, [] => .isFalse (by intro he; cases he)
    | x :: xs, y :: ys =>
        match Val.decEq x y, Val.decEqList xs ys with
        | .isTrue hx, .isTrue ht => .isTrue (by rw [hx, ht])
        | .isFalse hx, _ => .isFalse (by intro he; cases he; exact hx rfl)
        | _, .isFalse ht => .isFalse (by intro he; cases he; exact ht rfl)
end

instance : DecidableEq Val := Val.decEq

theorem sequenceItems?_seq (xs : Supply) : sequenceItems? (Val.seq xs) = some xs := rfl

theorem listItems?_list (xs : Supply) : listItems? (Val.list xs) = some xs := rfl

/-! ## Shared openable-structure projection (`structureItems?`)

`structureItems?` unifies the openable halves of `sequenceItems?` and
`listItems?`: both collection kinds project to their immediate items, and an
atom is not an openable structure. It matches the full model's
`Result.structureItems?`, the deconstruction receiver's structure view.
-/

theorem structureItems?_seq (xs : Supply) :
    structureItems? (Val.seq xs) = some xs := rfl

theorem structureItems?_list (xs : Supply) :
    structureItems? (Val.list xs) = some xs := rfl

theorem structureItems?_atom (n : Int) :
    structureItems? (Val.atom n) = none := rfl

/-- On sequence values the shared projection agrees with the kind-specific
one. -/
theorem structureItems?_eq_sequenceItems?_on_seq (xs : Supply) :
    structureItems? (Val.seq xs) = sequenceItems? (Val.seq xs) := rfl

/-- On list values the shared projection agrees with the kind-specific one. -/
theorem structureItems?_eq_listItems?_on_list (xs : Supply) :
    structureItems? (Val.list xs) = listItems? (Val.list xs) := rfl

/-- The structural projection with a one-item fallback is exactly the total
item view: `open` treats a non-structure as one item, and `openLoneStructure`
opens a single received value through this same expression. -/
theorem structureItems?_getD_eq_items (v : Val) :
    (structureItems? v).getD [v] = items v := by
  cases v <;> rfl

theorem items_seq (xs : Supply) : items (Val.seq xs) = xs := rfl

/-- Spread opens one LIST boundary exactly like one sequence boundary
(`[1, 2, 3]...` supplies the items). -/
theorem items_list (xs : Supply) : items (Val.list xs) = xs := rfl

/-- Spreading the empty sequence contributes no items. -/
theorem items_empty :
    items (Val.seq []) = [] := rfl

/-- Spreading the empty list contributes no items either. -/
theorem items_empty_list :
    items (Val.list []) = [] := rfl

/-- The two empty structures are exactly the zero-item spreads: `()` and `[]`
are the only values whose spread contributes nothing. -/
theorem items_eq_nil_iff (v : Val) :
    items v = [] ↔ v = Val.seq [] ∨ v = Val.list [] := by
  cases v with
  | atom n => simp [items]
  | seq xs => simp [items]
  | list xs => simp [items]

/-- Generic zero-item-spread neutrality at the supply level: a spread that
contributes no items leaves the surrounding item supply unchanged. -/
theorem open_zero_items_neutral {v : Val} (h : items v = [])
    (before after : Supply) :
    before ++ items v ++ after = before ++ after := by
  rw [h]; simp

/-- An empty spread contributes nothing to a surrounding item supply. -/
theorem spread_empty_neutral (before after : Supply) :
    before ++ items (Val.seq []) ++ after = before ++ after :=
  open_zero_items_neutral items_empty before after

/-- The list twin: `[]...` contributes nothing to a surrounding item supply. -/
theorem spread_empty_list_neutral (before after : Supply) :
    before ++ items (Val.list []) ++ after = before ++ after :=
  open_zero_items_neutral items_empty_list before after

theorem seq_items_seq (xs : Supply) : Val.seq (items (Val.seq xs)) = Val.seq xs := rfl

theorem seq_items_atom (n : Int) : Val.seq (items (Val.atom n)) = Val.seq [Val.atom n] := rfl

example : Val.seq (items (Val.atom 7)) ≠ Val.atom 7 := by decide

example : (Val.seq [Val.atom 1, Val.atom 2]) = (Val.seq [Val.atom 1, Val.atom 2]) := rfl

theorem nesting_matters :
    Val.seq [Val.atom 1, Val.seq [Val.atom 2, Val.atom 3]]
      ≠ Val.seq [Val.seq [Val.atom 1, Val.atom 2], Val.atom 3] := by
  decide

/-- A list value never equals the sequence value with the same elements: the
two collection kinds stay distinct. -/
theorem list_ne_seq (xs : Supply) : Val.list xs ≠ Val.seq xs := by
  intro he; cases he

theorem normalize_atom (n : Int) : normalize (Val.atom n) = Val.atom n := rfl

theorem normalize_empty : normalize (Val.seq []) = Val.seq [] := rfl

theorem normalize_singleton (v : Val) : normalize (Val.seq [v]) = normalize v := rfl

theorem normalize_nested_empty_collapses :
    normalize (Val.seq [Val.seq []]) = Val.seq [] := rfl

theorem normalize_deep_nested_empty_collapses :
  normalize (Val.seq [Val.seq [Val.seq []]]) = Val.seq [] := rfl

theorem normalize_keeps_pair (a b : Val) :
    normalize (Val.seq [a, b]) = Val.seq [normalize a, normalize b] := rfl

/-- List normalization is element-wise only: the boundary never collapses,
so `[7]` stays `[7]` and `[]` stays `[]`. -/
theorem normalize_list_exact (xs : Supply) :
    normalize (Val.list xs) = Val.list (normalizeList xs) := rfl

theorem normalize_singleton_list_kept (v : Val) :
    normalize (Val.list [v]) = Val.list [normalize v] := rfl

theorem capture_eq_normalize_seq (xs : Supply) :
    capture xs = normalize (Val.seq xs) := rfl

theorem capture_empty : capture [] = Val.seq [] := rfl

theorem capture_singleton (v : Val) : capture [v] = normalize v := rfl

theorem capture_singleton_empty : capture [Val.seq []] = Val.seq [] := rfl

theorem capture_singleton_atom (n : Int) : capture [Val.atom n] = Val.atom n := rfl

theorem capture_pair (a b : Val) :
    capture [a, b] = Val.seq [normalize a, normalize b] := rfl

theorem capture_singleton_atom_ne_seq :
    capture [Val.atom 1] ≠ Val.seq [Val.atom 1] := by
  decide

theorem sequenceItems?_capture_pair :
    sequenceItems? (capture [Val.atom 1, Val.atom 2])
      = some [Val.atom 1, Val.atom 2] := by
  decide

theorem sequenceItems?_capture_singleton_atom :
    sequenceItems? (capture [Val.atom 1]) = none := by
  decide

/-! ## Zero-item-spread neutrality (`()...` and `[]...`)

`Val.seq []` is the empty sequence value `()` and `Val.list []` is the empty
list value `[]`; their item views are the supplies of the explicit spreads
`()...` and `[]...`, and both contribute zero items (`items_empty`,
`items_empty_list` — by `items_eq_nil_iff` they are the only such values).
The theorems below lift that neutrality to the two receiver-purpose
materializations: `capture`, the canonical written-construction boundary, and
`collect`, the collecting-binding boundary. The core model does not model root
output, so the claims here are about item supplies and materialized values,
not output emission.
-/

/-- Generic neutral open at the capture boundary: any zero-item spread leaves
the captured value unchanged wherever it is inserted. -/
theorem capture_zero_item_spread_neutral {v : Val} (h : items v = [])
    (before after : Supply) :
    capture (before ++ items v ++ after) = capture (before ++ after) :=
  congrArg capture (open_zero_items_neutral h before after)

/-- Generic neutral open at the segment-collection boundary: any zero-item
spread leaves the collected list unchanged wherever it is inserted
(`first, ...rest = 1, 2, ()...` collects `rest = [2]`). -/
theorem collect_zero_item_spread_neutral {v : Val} (h : items v = [])
    (before after : Supply) :
    collect (before ++ items v ++ after) = collect (before ++ after) :=
  congrArg collect (open_zero_items_neutral h before after)

/-- An empty spread is neutral at a canonical capture or written-construction
boundary: `()...` contributes no items to the surrounding supply, so the
captured value is unchanged wherever the empty spread is inserted. -/
theorem capture_empty_spread_neutral
    (before after : Supply) :
    capture (before ++ items (Val.seq []) ++ after) =
      capture (before ++ after) :=
  capture_zero_item_spread_neutral items_empty before after

/-- The list twin: the empty-list spread `[]...` is equally neutral at the
capture boundary. -/
theorem capture_empty_list_spread_neutral
    (before after : Supply) :
    capture (before ++ items (Val.list []) ++ after) =
      capture (before ++ after) :=
  capture_zero_item_spread_neutral items_empty_list before after

/-- `(n, ()...) == n`. `Val.seq []` is the empty sequence value `()`,
`items (Val.seq [])` is its explicit spread `()...`, and the surrounding
`capture` is the canonical written-construction boundary. The spread
contributes zero items, so the boundary captures the one-item supply
`[Val.atom n]`, and singleton normalization returns the number itself
(`capture_singleton_atom`). The claim would not hold for the raw constructor:
`Val.seq [Val.atom n]` is deliberately distinct from `Val.atom n` before
canonicalization (`capture_singleton_atom_ne_seq`). -/
theorem capture_atom_empty_spread (n : Int) :
    capture ([Val.atom n] ++ items (Val.seq [])) = Val.atom n := by
  calc
    capture ([Val.atom n] ++ items (Val.seq []))
        = capture [Val.atom n] := by
          simpa using capture_empty_spread_neutral [Val.atom n] []
    _ = Val.atom n := capture_singleton_atom n

/-- `(n, []...) == n`: the list twin of `capture_atom_empty_spread` — the
empty-list spread is just as invisible to the captured value, even though the
unspread `[]` itself is a visible one-item value. -/
theorem capture_atom_empty_list_spread (n : Int) :
    capture ([Val.atom n] ++ items (Val.list [])) = Val.atom n := by
  calc
    capture ([Val.atom n] ++ items (Val.list []))
        = capture [Val.atom n] := by
          simpa using capture_empty_list_spread_neutral [Val.atom n] []
    _ = Val.atom n := capture_singleton_atom n

/-- `openLoneStructure` on a single-value supply is definitionally the shared
structural projection with a one-item fallback — the exact shape of the full
model's deconstruction binder (`(Result.structureItems? value).getD [value]`). -/
theorem openLoneStructure_single_eq_structureItems?_getD (v : Val) :
    openLoneStructure [v] = (structureItems? v).getD [v] := rfl

theorem openLoneStructure_empty : openLoneStructure [] = [] := rfl

theorem openLoneStructure_singleSeq (xs : Supply) :
    openLoneStructure [Val.seq xs] = xs := rfl

/-- Deconstruction opens a lone LIST exactly like a lone sequence value. -/
theorem openLoneStructure_singleList (xs : Supply) :
    openLoneStructure [Val.list xs] = xs := rfl

theorem openLoneStructure_singleAtom (n : Int) :
    openLoneStructure [Val.atom n] = [Val.atom n] := rfl

theorem openLoneStructure_multi (a b : Val) (rest : Supply) :
    openLoneStructure (a :: b :: rest) = a :: b :: rest := rfl

/-- The shared-projection implementation is extensionally identical to the
previous explicit sequence/list case split, for every possible supply. -/
theorem openLoneStructure_eq_explicit (xs : Supply) :
    openLoneStructure xs =
      match xs with
      | [Val.seq ys] => ys
      | [Val.list ys] => ys
      | other => other := by
  cases xs with
  | nil => rfl
  | cons v tail =>
      cases tail with
      | nil => cases v <;> rfl
      | cons w rest => simp [openLoneStructure]

theorem openLoneStructure_nested_empty_opens_one_boundary :
    openLoneStructure [Val.seq [Val.seq []]] = [Val.seq []] := rfl

/-! ## Lone-structure characterization (`loneStructure`)

`loneStructure` picks out exactly the supplies `openLoneStructure` rewrites —
a single sequence value or a single exact list value. The receiver theorems
later in this file split the whole receiver story on this predicate: outside
lone structures the call and deconstruction receivers agree; on lone
structures they never share a successful binding.
-/

theorem loneStructure_lone_seq (xs : Supply) :
    loneStructure [Val.seq xs] = true := rfl

theorem loneStructure_lone_list (xs : Supply) :
    loneStructure [Val.list xs] = true := rfl

theorem loneStructure_nil : loneStructure [] = false := rfl

theorem loneStructure_lone_atom (n : Int) :
    loneStructure [Val.atom n] = false := rfl

theorem loneStructure_multi (a b : Val) (rest : Supply) :
    loneStructure (a :: b :: rest) = false := rfl

/-- On single-value supplies the predicate is exactly "the value is an
openable structure". -/
theorem loneStructure_singleton (v : Val) :
    loneStructure [v] = (structureItems? v).isSome := rfl

/-- Specification: `loneStructure` holds exactly on `[Val.seq ys]` and
`[Val.list ys]` supplies. -/
theorem loneStructure_eq_true_iff (xs : Supply) :
    loneStructure xs = true ↔
      (∃ ys, xs = [Val.seq ys]) ∨ (∃ ys, xs = [Val.list ys]) := by
  constructor
  · intro h
    cases xs with
    | nil => exact Bool.noConfusion h
    | cons a t =>
      cases t with
      | cons b t2 => exact Bool.noConfusion h
      | nil =>
        cases a with
        | atom n => exact Bool.noConfusion h
        | seq ys => exact Or.inl ⟨ys, rfl⟩
        | list ys => exact Or.inr ⟨ys, rfl⟩
  · rintro (⟨ys, rfl⟩ | ⟨ys, rfl⟩) <;> rfl

/-- Outside the lone-structure shape, deconstruction's supply preparation is
the identity: nothing but a lone structure is ever opened. -/
theorem openLoneStructure_of_not_loneStructure {xs : Supply}
    (h : loneStructure xs = false) :
    openLoneStructure xs = xs := by
  cases xs with
  | nil => rfl
  | cons a t =>
    cases t with
    | cons b t2 => rfl
    | nil =>
      cases a with
      | atom n => rfl
      | seq ys => exact Bool.noConfusion h
      | list ys => exact Bool.noConfusion h

/-! ## Exact segment collection (`collect`)

`collect : Supply -> ListValue` is the collecting-binding operation.
The laws below establish the required exactness properties: stable result
kind, exact length and elements, singleton preservation, the open/collect
round trip, and provenance independence. They intentionally supersede the
pre-list `captureVariadic := capture` coincidence model.
-/

/-- Stable result kind + exact elements: `collect` always produces the exact
list of precisely the assigned items (`listItems?` is total on collect
results — a section law that `capture` deliberately fails on singletons). -/
theorem collect_is_list (xs : Supply) : listItems? (collect xs) = some xs := rfl

/-- Exact length: collecting never adds, drops, or merges items. -/
theorem collect_length (xs : Supply) : (items (collect xs)).length = xs.length := rfl

/-- Zero assigned items collect to the empty list `[]` — a visible exact
value, never the empty sequence value `()`. -/
theorem collect_empty : collect [] = Val.list [] := rfl

theorem collect_empty_ne_empty_seq : collect [] ≠ Val.seq [] := by decide

/-- Singleton preservation: one assigned item collects to the one-element
list `[v]`, for every value kind. -/
theorem collect_singleton (v : Val) : collect [v] = Val.list [v] := rfl

/-- Singleton preservation for a grouped sequence value of ANY payload:
`first, ...rest = 1, (…)` collects `rest = [(…)]`. -/
theorem collect_singleton_seq (ys : Supply) :
    collect [Val.seq ys] = Val.list [Val.seq ys] := rfl

/-- Singleton preservation for an exact list value of ANY payload:
`first, ...rest = 1, […]` collects `rest = [[…]]`. -/
theorem collect_singleton_list (ys : Supply) :
    collect [Val.list ys] = Val.list [Val.list ys] := rfl

example : collect [Val.atom 7] = Val.list [Val.atom 7] := rfl
example : collect [Val.seq []] = Val.list [Val.seq []] := rfl
example : collect [Val.list []] = Val.list [Val.list []] := rfl
example : collect [Val.seq [Val.atom 2, Val.atom 3]]
    = Val.list [Val.seq [Val.atom 2, Val.atom 3]] := rfl
example : collect [Val.list [Val.atom 2, Val.atom 3]]
    = Val.list [Val.list [Val.atom 2, Val.atom 3]] := rfl

/-- No value is an element of its own payload list: an element of `ys` is
structurally smaller than `Val.seq ys`. -/
theorem mem_ne_seq {w : Val} {ys : List Val} (h : w ∈ ys) : w ≠ Val.seq ys := by
  intro he
  have hlt : sizeOf w < sizeOf ys := List.sizeOf_lt_of_mem h
  have hsz : sizeOf (Val.seq ys) = 1 + sizeOf ys := by simp
  rw [he, hsz] at hlt
  omega

/-- The list twin of `mem_ne_seq`. -/
theorem mem_ne_list {w : Val} {ys : List Val} (h : w ∈ ys) : w ≠ Val.list ys := by
  intro he
  have hlt : sizeOf w < sizeOf ys := List.sizeOf_lt_of_mem h
  have hsz : sizeOf (Val.list ys) = 1 + sizeOf ys := by simp
  rw [he, hsz] at hlt
  omega

/-- A singleton collected segment is NEVER erased to its item: `collect [v] ≠ v`. This is
the load-bearing difference from canonical capture (`capture [v] = normalize v`),
and what keeps one remaining structured row distinct from the row's own
elements. -/
theorem collect_singleton_ne_item (v : Val) : collect [v] ≠ v := by
  intro he
  exact absurd he.symm (mem_ne_list List.mem_cons_self)

/-- `collect` and `capture` are different operations on the same supply. -/
theorem collect_singleton_atom_ne_capture (n : Int) :
    collect [Val.atom n] ≠ capture [Val.atom n] := by
  intro he
  rw [capture_singleton_atom] at he
  exact collect_singleton_ne_item (Val.atom n) he

/-! ### Round-trip laws

The three receiver-purpose operations compose as partial inverses, each on
its own domain:

* `spread ∘ collect = id` on supplies — `items_collect`;
* `collect ∘ open = id` on exact list values — `collect_items_list`;
* `capture ∘ open = id` on canonical non-list values —
  `capture_items_of_canonical` (later in this file; spreading a list and
  re-CAPTURING converts it to the sequence world, `capture_items_of_list`,
  so the unrestricted claim would be false).
-/

/-- Open/collect round trip: surface spread (`items`, the `open` operation)
re-supplies EXACTLY the collected items, so variadic forwarding
(`Forward(...items) = Target(items...)`) is ordinary list spread. -/
theorem items_collect (xs : Supply) : items (collect xs) = xs := rfl

/-- Collect/open round trip on the list side: re-collecting a spread list's
items reproduces the list exactly — `collect` is a section of `open` on exact
list values. Definitionally trivial, conceptually load-bearing: a collecting binding that
re-collects a forwarded collected list's spread observes the original list. -/
theorem collect_items_list (xs : Supply) :
    collect (items (Val.list xs)) = Val.list xs := rfl

/-- Provenance independence: `collect` depends only on the assembled item
supply, never on which structures were spread to produce it. Collecting the
concatenation of two spread supplies is exactly the list of those items,
whatever `a` and `b` were (`first, ...rest = 1, [2, 3]..., (4, 5)...` gives
`rest = [2, 3, 4, 5]`). -/
theorem collect_spread_concat_exact (a b : Val) :
    collect (items a ++ items b) = Val.list (items a ++ items b) := rfl

/-- Equal supplies collect equal lists — the general form of provenance
independence (a function of the supply alone). -/
theorem collect_congr {xs ys : Supply} (h : xs = ys) : collect xs = collect ys :=
  congrArg collect h

/-- Grouped and spread supplies collect DIFFERENT values: `collect` of one
grouped sequence value is the one-element list holding it, never the collect
of its stored items (unless the sequence were its own element, which the
structural order excludes). Supersedes the obsolete coincidence
`captureVariadic [Val.seq ys] = captureVariadic ys` of the pre-list model. -/
theorem collect_lone_seq_ne_collect_items (ys : Supply) :
    collect [Val.seq ys] ≠ collect (items (Val.seq ys)) := by
  intro he
  have hpay : [Val.seq ys] = ys := by
    simpa [collect, items] using he
  cases ys with
  | nil => cases hpay
  | cons w t =>
      have hw : Val.seq (w :: t) = w := by
        have := List.cons.inj hpay
        exact this.1
      have ht : t = [] := by
        have := List.cons.inj hpay
        simpa using this.2.symm
      subst ht
      exact absurd hw.symm (mem_ne_seq List.mem_cons_self)

/-- The list twin: a grouped list argument and its spread items collect
different values as well. -/
theorem collect_lone_list_ne_collect_items (ys : Supply) :
    collect [Val.list ys] ≠ collect (items (Val.list ys)) := by
  intro he
  have hpay : [Val.list ys] = ys := by
    simpa [collect, items] using he
  cases ys with
  | nil => cases hpay
  | cons w t =>
      have hw : Val.list (w :: t) = w := by
        have := List.cons.inj hpay
        exact this.1
      have ht : t = [] := by
        have := List.cons.inj hpay
        simpa using this.2.symm
      subst ht
      exact absurd hw.symm (mem_ne_list List.mem_cons_self)

/-! ## Binding checks -/

theorem collecting_tail :
    bindArgs [Pat.name "x", Pat.collecting "rest"] [Val.atom 1, Val.atom 2, Val.atom 3]
      = some [("x", Val.atom 1), ("rest", Val.list [Val.atom 2, Val.atom 3])] := by
  decide

theorem collecting_empty :
    bindArgs [Pat.name "x", Pat.collecting "rest"] [Val.atom 1]
      = some [("x", Val.atom 1), ("rest", Val.list [])] := by
  decide

theorem collecting_head :
    bindArgs [Pat.collecting "head", Pat.name "last"] [Val.atom 1, Val.atom 2, Val.atom 3]
      = some [("head", Val.list [Val.atom 1, Val.atom 2]), ("last", Val.atom 3)] := by
  decide

theorem collecting_middle :
    bindArgs [Pat.name "first", Pat.collecting "middle", Pat.name "last"]
        [Val.atom 1, Val.atom 2, Val.atom 3, Val.atom 4]
      = some [("first", Val.atom 1),
              ("middle", Val.list [Val.atom 2, Val.atom 3]),
              ("last", Val.atom 4)] := by
  decide

/-- A one-item collected segment stays a one-element list: no singleton collapse
(the pre-list model bound `rest = 2` here; exact collection binds `[2]`). -/
theorem collecting_singleton_collected :
    bindArgs [Pat.name "x", Pat.collecting "rest"] [Val.atom 1, Val.atom 2]
      = some [("x", Val.atom 1), ("rest", Val.list [Val.atom 2])] := by
  decide

theorem call_bind_collecting_does_not_open_lone_sequence :
    bindArgs [Pat.name "x", Pat.collecting "rest"] [Val.seq [Val.atom 1, Val.atom 2, Val.atom 3]]
      = some [("x", Val.seq [Val.atom 1, Val.atom 2, Val.atom 3]), ("rest", Val.list [])] := by
  decide

-- Assignment deconstruction is an unpacking receiver: a single stored sequence
-- or list value is opened and matched element-by-element. Function calls
-- (`bindArgs`) do NOT open. These checks pin that contrast.

/-- `Add(A)` / function parameter binding: a single sequence-valued argument against
two fixed parameters is an arity error — the call binder does not open `A`. -/
theorem args_fixed_single_sequence_rejected :
    bindArgs [Pat.name "x", Pat.name "y"]
      [Val.seq [Val.atom 1, Val.atom 2]]
      = none := by
  decide

/-- The list twin: `Add(A)` with a stored list is an arity error too. -/
theorem args_fixed_single_list_rejected :
    bindArgs [Pat.name "x", Pat.name "y"]
      [Val.list [Val.atom 1, Val.atom 2]]
      = none := by
  decide

/-- `x, y = A`: deconstruction opens the single sequence-valued right-hand side, so
the two targets bind `x = 1`, `y = 2`. -/
theorem deconstruct_fixed_single_sequence_opens :
    bindDeconstruct [Pat.name "x", Pat.name "y"]
      [Val.seq [Val.atom 1, Val.atom 2]]
      = some [("x", Val.atom 1), ("y", Val.atom 2)] := by
  decide

/-- `x, y = [1, 2]`: deconstruction opens a lone LIST the same way. -/
theorem deconstruct_fixed_single_list_opens :
    bindDeconstruct [Pat.name "x", Pat.name "y"]
      [Val.list [Val.atom 1, Val.atom 2]]
      = some [("x", Val.atom 1), ("y", Val.atom 2)] := by
  decide

/-- `x, y = A...`: the explicit spread supplies `A`'s items directly, which bind the
two fixed targets — the same result as the bare unpack. (`items` is the surface
`...` view.) -/
theorem deconstruct_fixed_explicit_spread_succeeds :
    bindDeconstruct [Pat.name "x", Pat.name "y"]
      (items (Val.seq [Val.atom 1, Val.atom 2]))
      = some [("x", Val.atom 1), ("y", Val.atom 2)] := by
  decide

/-- `first, ...rest = A`: deconstruction opens `A`, so `first = 1` and the collecting binding
COLLECTS the remaining items as the exact list `[2, 3]`. -/
theorem deconstruct_collecting_single_sequence_opens :
    bindDeconstruct [Pat.name "first", Pat.collecting "rest"]
      [Val.seq [Val.atom 1, Val.atom 2, Val.atom 3]]
      = some [("first", Val.atom 1),
              ("rest", Val.list [Val.atom 2, Val.atom 3])] := by
  decide

/-- `first, ...rest = [1, 2, 3]`: the lone-list right-hand side opens the same
way, and the collecting binding collects `[2, 3]`. -/
theorem deconstruct_collecting_single_list_opens :
    bindDeconstruct [Pat.name "first", Pat.collecting "rest"]
      [Val.list [Val.atom 1, Val.atom 2, Val.atom 3]]
      = some [("first", Val.atom 1),
              ("rest", Val.list [Val.atom 2, Val.atom 3])] := by
  decide

/-- `first, ...rest = A...`: the explicit spread supplies the same spread items as
the bare unpack above. -/
theorem deconstruct_collecting_explicit_spread :
    bindDeconstruct [Pat.name "first", Pat.collecting "rest"]
      (items (Val.seq [Val.atom 1, Val.atom 2, Val.atom 3]))
      = some [("first", Val.atom 1),
              ("rest", Val.list [Val.atom 2, Val.atom 3])] := by
  decide

/-- Deconstruction opens where the call binder preserves: on a single stored
sequence value the two modes disagree, so they are not the same function. -/
theorem deconstruct_opens_where_args_preserves :
    bindDeconstruct [Pat.name "x", Pat.name "y"] [Val.seq [Val.atom 1, Val.atom 2]]
      ≠ bindArgs [Pat.name "x", Pat.name "y"] [Val.seq [Val.atom 1, Val.atom 2]] := by
  decide

theorem fixed_arity_mismatch_rejected :
    bindArgs [Pat.name "x", Pat.name "y"] [Val.atom 1] = none := by
  decide

theorem fixed_arity_surplus_rejected :
    bindArgs [Pat.name "x", Pat.name "y"] [Val.atom 1, Val.atom 2, Val.atom 3] = none := by
  decide

theorem two_collecting_bindings_rejected :
    bindPats [Pat.collecting "a", Pat.collecting "b"] [Val.atom 1, Val.atom 2] = none := by
  decide

/--
The lone collecting pattern models both the single variadic parameter
`F(...items)` and the lone-collecting assignment `...x = 1, 2, 3`, which
reaches this binder through the deconstruction receiver.
-/
theorem variadic_is_lone_collecting (xs : Supply) :
    bindArgs [Pat.collecting "x"] xs = some [("x", collect xs)] := by
  unfold bindArgs
  simp [bindPats, bindFixed, Pat.isCollecting, Pat.key, List.take_length, List.drop_length]

/-! ## Generic segment collection (the `bindPats` split theorem)

The concrete binding checks above pin specific shapes; the theorems below
establish the general law. For EVERY parameter list with exactly one collecting binding —
written `front ++ Pat.collecting r :: back` with collecting-free `front` and `back` — and
every sufficiently long supply, the bind SUCCEEDS and the environment is,
structurally, the front captures, then the collecting binding bound to `collect` of
exactly the middle supply, then the back captures. Leading, middle, trailing,
and lone-collecting shapes and empty/singleton/multiple middles are all instances.

The environment is stated structurally (an association list assembled
positionally), so no name-uniqueness premise is needed: duplicate names in
this abstract binder simply contribute multiple entries, and surface KatLang
separately rejects duplicate parameter names before this model is reached.
(The full model's binder additionally MERGES duplicate bindings with an
equality check — `mergeEqualValEnv` — which the extraction deliberately
omits; the bridge theorems in `KatLangArityLaws.lean` use distinct names.)
-/

private theorem filter_isCollecting_eq_nil : ∀ {ps : List Pat},
    (∀ p ∈ ps, p.isCollecting = false) -> ps.filter Pat.isCollecting = []
  | [], _ => rfl
  | p :: ps, h => by
      have hp := h p List.mem_cons_self
      have ih := filter_isCollecting_eq_nil (ps := ps)
        (fun q hq => h q (List.mem_cons_of_mem p hq))
      simp [hp, ih]

private theorem filter_isCollecting_single_collecting (front back : List Pat) (r : String)
    (hf : ∀ p ∈ front, p.isCollecting = false) (hb : ∀ p ∈ back, p.isCollecting = false) :
    (front ++ Pat.collecting r :: back).filter Pat.isCollecting = [Pat.collecting r] := by
  rw [List.filter_append, filter_isCollecting_eq_nil hf]
  simp [Pat.isCollecting, filter_isCollecting_eq_nil hb]

private theorem findIdx?_isCollecting_first_collecting : ∀ (front : List Pat) (r : String)
    (back : List Pat), (∀ p ∈ front, p.isCollecting = false) ->
    (front ++ Pat.collecting r :: back).findIdx? Pat.isCollecting = some front.length
  | [], r, back, _ => by simp [List.findIdx?_cons, Pat.isCollecting]
  | p :: front, r, back, h => by
      have hp := h p List.mem_cons_self
      have ih := findIdx?_isCollecting_first_collecting front r back
        (fun q hq => h q (List.mem_cons_of_mem p hq))
      simp [List.findIdx?_cons, hp, ih]

private theorem take_length_append {A : Type} : ∀ (front tail : List A),
    (front ++ tail).take front.length = front
  | [], _ => rfl
  | a :: front, tail => by simp [take_length_append front tail]

private theorem drop_length_append {A : Type} : ∀ (front tail : List A),
    (front ++ tail).drop front.length = tail
  | [], _ => rfl
  | a :: front, tail => by simp [drop_length_append front tail]

private theorem drop_length_succ_append {A : Type} : ∀ (front : List A) (x : A)
    (tail : List A), (front ++ x :: tail).drop (front.length + 1) = tail
  | [], _, _ => rfl
  | a :: front, x, tail => by simp [drop_length_succ_append front x tail]

/-- The split form of the general collecting-binding law: under the binder's
ordinary length condition, binding `front ++ collecting r :: back` against `xs`
succeeds with the exact `take`/`drop` allocation — front captures from the
front, back captures from the back, and the collecting binding bound to `collect` of
precisely the remaining middle. -/
theorem bindPats_collecting_split (front back : List Pat) (r : String) (xs : Supply)
    (hf : ∀ p ∈ front, p.isCollecting = false)
    (hb : ∀ p ∈ back, p.isCollecting = false)
    (hlen : front.length + back.length ≤ xs.length) :
    bindPats (front ++ Pat.collecting r :: back) xs
      = some (bindFixed front (xs.take front.length)
          ++ (r, collect ((xs.drop front.length).take
                (xs.length - back.length - front.length)))
             :: bindFixed back (xs.drop (xs.length - back.length))) := by
  have hfilter := filter_isCollecting_single_collecting front back r hf hb
  have hfind := findIdx?_isCollecting_first_collecting front r back hf
  simp only [bindPats, hfilter, hfind, take_length_append,
    drop_length_succ_append, Pat.key, List.length_append, List.length_cons]
  simp
  omega

/-- The supplied-slots form of the general collecting-binding law: when the supply
is written as `frontVals ++ mid ++ backVals` with lengths matching the fixed
captures, the environment is EXACTLY the front bindings, the collecting binding bound
to `collect mid`, and the back bindings — for every middle supply (empty,
singleton, or many) and every leading/middle/trailing collecting position. -/
theorem bindPats_collect_exact (front back : List Pat) (r : String)
    (frontVals mid backVals : Supply)
    (hf : ∀ p ∈ front, p.isCollecting = false)
    (hb : ∀ p ∈ back, p.isCollecting = false)
    (hfl : frontVals.length = front.length)
    (hbl : backVals.length = back.length) :
    bindPats (front ++ Pat.collecting r :: back) (frontVals ++ mid ++ backVals)
      = some (bindFixed front frontVals
          ++ (r, collect mid) :: bindFixed back backVals) := by
  have hlen : front.length + back.length ≤ (frontVals ++ mid ++ backVals).length := by
    simp only [List.length_append]
    omega
  have htake : (frontVals ++ mid ++ backVals).take front.length = frontVals := by
    rw [← hfl, List.append_assoc, take_length_append]
  have hdropf : (frontVals ++ mid ++ backVals).drop front.length = mid ++ backVals := by
    rw [← hfl, List.append_assoc, drop_length_append]
  have hmidlen : (frontVals ++ mid ++ backVals).length - back.length - front.length
      = mid.length := by
    simp only [List.length_append]
    omega
  have hbacklen : (frontVals ++ mid ++ backVals).length - back.length
      = (frontVals ++ mid).length := by
    simp only [List.length_append]
    omega
  rw [bindPats_collecting_split front back r _ hf hb hlen, htake, hdropf, hmidlen,
    take_length_append, hbacklen, drop_length_append]

/-- Trailing collecting binding (`Tail(first, ...rest)`), for every middle supply. -/
theorem bindPats_trailing_collecting (a : String) (x : Val) (r : String) (mid : Supply) :
    bindPats [Pat.name a, Pat.collecting r] (x :: mid)
      = some [(a, x), (r, collect mid)] := by
  have h := bindPats_collect_exact [Pat.name a] [] r [x] mid []
    (by intro p hp; simp at hp; simp [hp, Pat.isCollecting])
    (by intro p hp; simp at hp)
    rfl rfl
  simpa [bindFixed] using h

/-- Leading collecting binding (`Init(...init, last)`), for every middle supply. -/
theorem bindPats_leading_collecting (r : String) (mid : Supply) (z : String) (y : Val) :
    bindPats [Pat.collecting r, Pat.name z] (mid ++ [y])
      = some [(r, collect mid), (z, y)] := by
  have h := bindPats_collect_exact [] [Pat.name z] r [] mid [y]
    (by intro p hp; simp at hp)
    (by intro p hp; simp at hp; simp [hp, Pat.isCollecting])
    rfl rfl
  simpa [bindFixed] using h

/-- Middle collecting binding (`F(x, ...y, z)`), for every middle supply. -/
theorem bindPats_middle_collecting (a : String) (x : Val) (r : String) (mid : Supply)
    (z : String) (y : Val) :
    bindPats [Pat.name a, Pat.collecting r, Pat.name z] (x :: (mid ++ [y]))
      = some [(a, x), (r, collect mid), (z, y)] := by
  have h := bindPats_collect_exact [Pat.name a] [Pat.name z] r [x] mid [y]
    (by intro p hp; simp at hp; simp [hp, Pat.isCollecting])
    (by intro p hp; simp at hp; simp [hp, Pat.isCollecting])
    rfl rfl
  simpa [bindFixed] using h

/-- Lone collecting binding (`F(...items)`), re-derived as the degenerate split instance —
agrees with the directly proved `variadic_is_lone_collecting`/`bindArgs_lone_collecting`. -/
theorem bindPats_lone_collecting (r : String) (xs : Supply) :
    bindPats [Pat.collecting r] xs = some [(r, collect xs)] := by
  have h := bindPats_collect_exact [] [] r [] xs []
    (by intro p hp; simp at hp)
    (by intro p hp; simp at hp)
    rfl rfl
  simpa [bindFixed] using h

/-! ## Receiver theorems

The concrete checks above pin the call/deconstruction contrast on specific
values. The theorems below establish the contrast in general, split exactly
on the `loneStructure` predicate:

* `receivers_agree_outside_lone_structure` — on every supply with
  `loneStructure xs = false` the two receivers are the SAME function, so the
  entire receiver asymmetry is confined to the lone-structure case;
* `deconstruct_singleton_eq_args_items` — on a single-value supply the
  deconstruction receiver binds exactly what the CALL receiver binds on the
  value's immediate item view. This is a receiver-level equation, not an
  unrestricted surface equivalence with a written deconstruction RHS spread:
  the surface spread passes through `capture` before deconstruction sees its
  single shared value (`deconstruct_spread_capture_can_open_further` pins the
  boundary-sensitive counterexample);
* `receivers_never_same_on_lone_structure` — on every lone-structure supply
  (`[Val.seq ys]` and `[Val.list ys]` alike) the two receivers NEVER both
  succeed with the same environment, for any pattern list. The corollaries
  `receivers_never_agree_on_lone_seq` / `receivers_never_agree_on_lone_list`
  are the per-kind instances. This unified statement replaces the pre-list
  characterization (`agree_on_lone_seq_iff_lone_rest`), whose lone-collecting
  agreement depended on the canonical-capture coincidence: exact segment
  collection distinguishes the grouped argument (`rest = [A]`) from the
  spread items (`rest = [a1, …]`), so even the lone-collecting shape disagrees;
* the theorem is deliberately about shared SUCCESS, not Option inequality:
  both receivers can fail identically on a lone structure (see the example
  after the corollaries), so `bindArgs ps xs ≠ bindDeconstruct ps xs` would
  be false as a general lone-structure claim;
* `lone_collecting_disagrees_on_lone_list` — the concrete lone-collecting disagreement on
  a lone LIST supply (there both modes DO succeed, so the Option values
  really differ).
-/

/-- The deconstruction receiver's implicit opening of a single-value supply is
the total item view `items` — the same item supply the surface spread `...`
provides (`structureItems?` with the one-item scalar fallback). -/
theorem openLoneStructure_singleton (v : Val) : openLoneStructure [v] = items v :=
  structureItems?_getD_eq_items v

/-- Localization: outside the lone-structure shape the call and deconstruction
receivers agree — deconstruction's extra behaviour is confined to
`loneStructure` supplies. -/
theorem receivers_agree_outside_lone_structure (ps : List Pat) (xs : Supply)
    (h : loneStructure xs = false) :
    bindDeconstruct ps xs = bindArgs ps xs := by
  unfold bindDeconstruct bindArgs
  rw [openLoneStructure_of_not_loneStructure h]

/-- Receiver/item-view equation: on a single-value supply, deconstruction binds
exactly what a call binds on the value's immediate item view. A written spread
on an assignment RHS additionally passes through `capture`; the next theorem
pins why this equation must not be presented as an unrestricted surface
rewrite. -/
theorem deconstruct_singleton_eq_args_items (ps : List Pat) (v : Val) :
    bindDeconstruct ps [v] = bindArgs ps (items v) := by
  unfold bindDeconstruct bindArgs
  rw [openLoneStructure_singleton]

/-- Surface-capture boundary counterexample. Let `A = [(1, 2)]`. Bare
deconstruction of `A` opens the outer list once and leaves the sequence row as
one item, so two fixed targets fail. A written `A...` first supplies that row
to the assignment's ordinary capture boundary; singleton capture returns the
row itself, after which deconstruction opens it and the two targets succeed.
The core intentionally exposes the operations needed to state this boundary
effect without modeling parser elaboration as another evaluator. -/
theorem deconstruct_spread_capture_can_open_further :
    let row := Val.seq [Val.atom 1, Val.atom 2]
    let a := Val.list [row]
    let ps := [Pat.name "x", Pat.name "y"]
    bindDeconstruct ps [a] = none ∧
      bindDeconstruct ps [capture (items a)] =
        some [("x", Val.atom 1), ("y", Val.atom 2)] := by
  decide

/-- `variadic_is_lone_collecting`, generalized to an arbitrary collecting-binding name. -/
theorem bindArgs_lone_collecting (r : String) (xs : Supply) :
    bindArgs [Pat.collecting r] xs = some [(r, collect xs)] := by
  unfold bindArgs
  simp [bindPats, bindFixed, Pat.isCollecting, Pat.key, List.take_length, List.drop_length]

/-- Grouped/spread DISTINCTION for a single variadic parameter: `F(A)` with
a stored sequence `A` binds `rest = [A]` (one collected argument), while
`F(A...)` binds `rest = [a1, …, an]` (the collected spread items) — always
different bindings. Supersedes the obsolete paper theorem
`variadic_capture_unchanged_by_spread`. -/
theorem variadic_collect_distinguishes_spread (r : String) (ys : Supply) :
    bindArgs [Pat.collecting r] [Val.seq ys]
      ≠ bindArgs [Pat.collecting r] (items (Val.seq ys)) := by
  rw [bindArgs_lone_collecting, bindArgs_lone_collecting]
  intro he
  have hv : collect [Val.seq ys] = collect (items (Val.seq ys)) := by
    have := Option.some.inj he
    have hpair := List.cons.inj this
    have := congrArg Prod.snd hpair.1
    simpa [items] using this
  exact collect_lone_seq_ne_collect_items ys (by simpa [items] using hv)

/-- Exact bound value, grouped side: `F(A)` binds `r` to `collect [A]` — the
one-element list holding the grouped argument. -/
theorem variadic_collect_value_grouped (r : String) (ys : Supply) :
    bindArgs [Pat.collecting r] [Val.seq ys]
      = some [(r, Val.list [Val.seq ys])] :=
  bindArgs_lone_collecting r [Val.seq ys]

/-- Exact bound value, spread side: `F(A...)` binds `r` to `collect ys` — the
exact list of `A`'s stored items. -/
theorem variadic_collect_value_spread (r : String) (ys : Supply) :
    bindArgs [Pat.collecting r] (items (Val.seq ys))
      = some [(r, Val.list ys)] :=
  bindArgs_lone_collecting r ys

/-- The shared binder fails whenever the supply is at least two items shorter
than the pattern list: even a collecting binding cannot stand in for two missing
fixed positions. -/
theorem bindPats_none_of_undersupplied (ps : List Pat) (xs : Supply)
    (h : xs.length + 1 < ps.length) : bindPats ps xs = none := by
  unfold bindPats
  split
  · exact if_neg (by omega)
  · cases hidx : ps.findIdx? Pat.isCollecting with
    | none => rfl
    | some i => exact if_pos (by omega)
  · rfl

private theorem list_payload_not_self (ys : List Val) (hkind : Val) (hpay : [hkind] = ys)
    (hmem : ∀ w ∈ ys, w ≠ hkind) : False := by
  cases ys with
  | nil => cases hpay
  | cons w t =>
      have hw : hkind = w := (List.cons.inj hpay).1
      exact absurd hw.symm (hmem w List.mem_cons_self)

/-- The engine of the unified lone-structure theorem: for a single-value call
supply `[v]` and ANY deconstruction supply `ys` avoiding `v` (no member of
`ys` equals `v` — instantiated with a structure's own payload, which cannot
contain the structure), the call binder on `[v]` and the shared binder on
`ys` never both succeed with the same environment, for every pattern list.
Each successful agreement would force some member of `ys` to BE `v` (fixed
positions bind `v` on the call side and members of `ys` on the other) or
force `[v] = ys` (the lone-collecting shape collects both sides), contradicting the
avoidance premise. -/
private theorem receivers_never_same_on_singleton (ps : List Pat) (v : Val)
    (ys : Supply) (hmem : ∀ w ∈ ys, w ≠ v) :
    ¬ ∃ env, bindArgs ps [v] = some env ∧ bindPats ps ys = some env := by
  rintro ⟨env, hA, hD⟩
  cases ps with
  | nil =>
    simp [bindArgs, bindPats] at hA
  | cons p ps1 =>
    cases ps1 with
    | nil =>
      cases p with
      | collecting r =>
        rw [bindArgs_lone_collecting] at hA
        rw [show bindPats [Pat.collecting r] ys = bindArgs [Pat.collecting r] ys from rfl,
            bindArgs_lone_collecting] at hD
        rw [← hA] at hD
        have hv : collect ys = collect [v] := by
          have := Option.some.inj hD
          have hpair := List.cons.inj this
          simpa using congrArg Prod.snd hpair.1
        have hpay : [v] = ys := by
          simpa [collect] using hv.symm
        exact list_payload_not_self ys v hpay hmem
      | name x =>
        have eA : bindArgs [Pat.name x] [v]
            = some [(x, v)] := rfl
        rw [eA] at hA
        cases ys with
        | nil =>
          have h0 : bindPats [Pat.name x] ([] : Supply) = none := rfl
          rw [h0] at hD
          cases hD
        | cons w t =>
          cases t with
          | nil =>
            have eD : bindPats [Pat.name x] [w] = some [(x, w)] := rfl
            rw [eD] at hD
            rw [← hA] at hD
            simp at hD
            have hne : w ≠ v := hmem w List.mem_cons_self
            first
            | exact absurd hD hne
            | exact absurd hD.symm hne
          | cons b t2 =>
            have h0 : bindPats [Pat.name x] (w :: b :: t2) = none := by
              unfold bindPats
              simp [Pat.isCollecting]
            rw [h0] at hD
            cases hD
    | cons q ps2 =>
      cases ps2 with
      | nil =>
        cases p with
        | name x =>
          cases q with
          | name y =>
            simp [bindArgs, bindPats, Pat.isCollecting] at hA
          | collecting r =>
            have eA : bindArgs [Pat.name x, Pat.collecting r] [v]
                = some [(x, v), (r, Val.list [])] := rfl
            rw [eA] at hA
            cases ys with
            | nil =>
              have h0 : bindPats [Pat.name x, Pat.collecting r] ([] : Supply) = none := rfl
              rw [h0] at hD
              cases hD
            | cons w t =>
              have eD : bindPats [Pat.name x, Pat.collecting r] (w :: t)
                  = some [(x, w), (r, collect t)] := by
                simp [bindPats, Pat.isCollecting, Pat.key, bindFixed,
                      show List.findIdx? Pat.isCollecting [Pat.name x, Pat.collecting r]
                        = some 1 from rfl]
              rw [eD] at hD
              rw [← hD] at hA
              simp at hA
              have hne : w ≠ v := hmem w List.mem_cons_self
              first
              | exact absurd hA.1 hne
              | exact absurd hA.1.symm hne
        | collecting r =>
          cases q with
          | collecting b =>
            simp [bindArgs, bindPats, Pat.isCollecting] at hA
          | name y =>
            have eA : bindArgs [Pat.collecting r, Pat.name y] [v]
                = some [(r, Val.list []), (y, v)] := rfl
            rw [eA] at hA
            cases ys with
            | nil =>
              have h0 : bindPats [Pat.collecting r, Pat.name y] ([] : Supply) = none := rfl
              rw [h0] at hD
              cases hD
            | cons w t =>
              have eD : bindPats [Pat.collecting r, Pat.name y] (w :: t)
                  = some ((r, collect ((w :: t).take t.length))
                      :: bindFixed [Pat.name y] ((w :: t).drop t.length)) := by
                simp [bindPats, Pat.isCollecting, Pat.key, bindFixed,
                      show List.findIdx? Pat.isCollecting [Pat.collecting r, Pat.name y]
                        = some 0 from rfl]
              rw [eD] at hD
              rw [← hD] at hA
              cases hbv : (w :: t).drop t.length with
              | nil =>
                rw [hbv] at hA
                simp [bindFixed] at hA
              | cons b bs =>
                rw [hbv] at hA
                simp [bindFixed, Pat.key] at hA
                have hbdrop : b ∈ (w :: t).drop t.length := by
                  rw [hbv]
                  exact List.mem_cons_self
                have hbmem : b ∈ (w :: t) := by
                  first
                  | exact List.mem_of_mem_drop hbdrop
                  | exact List.drop_subset _ _ hbdrop
                  | exact List.drop_subset _ hbdrop
                have hne : b ≠ v := hmem b hbmem
                first
                | exact absurd hA.2 hne
                | exact absurd hA.2.symm hne
                | exact absurd hA.2.1 hne
                | exact absurd hA.2.1.symm hne
      | cons s ps3 =>
        have hnone : bindPats (p :: q :: s :: ps3) [v] = none := by
          apply bindPats_none_of_undersupplied
          simp
        rw [bindArgs] at hA
        rw [hnone] at hA
        cases hA

/-- Receiver non-coincidence on a lone structure, in full generality: for
EVERY pattern list and BOTH structure kinds (`[Val.seq ys]` and
`[Val.list ys]`), the call receiver and the deconstruction receiver never
both succeed with the same environment. The pre-list model's lone-collecting
agreement was a canonical-capture coincidence; exact segment collection removes
it. (Shared success is the strongest correct claim: both receivers CAN fail
identically on a lone structure, so plain Option inequality would be false —
see the example below.) -/
theorem receivers_never_same_on_lone_structure (ps : List Pat) (xs : Supply)
    (h : loneStructure xs = true) :
    ¬ ∃ env, bindArgs ps xs = some env ∧ bindDeconstruct ps xs = some env := by
  cases xs with
  | nil => exact Bool.noConfusion h
  | cons a t =>
    cases t with
    | cons b t2 => exact Bool.noConfusion h
    | nil =>
      cases a with
      | atom n => exact Bool.noConfusion h
      | seq ys =>
        simp only [bindDeconstruct, openLoneStructure_singleSeq]
        exact receivers_never_same_on_singleton ps (Val.seq ys) ys
          (fun w hw => mem_ne_seq hw)
      | list ys =>
        simp only [bindDeconstruct, openLoneStructure_singleList]
        exact receivers_never_same_on_singleton ps (Val.list ys) ys
          (fun w hw => mem_ne_list hw)

/-- Sequence-kind corollary of `receivers_never_same_on_lone_structure`. -/
theorem receivers_never_agree_on_lone_seq (ps : List Pat) (ys : List Val) :
    ¬ ∃ env, bindArgs ps [Val.seq ys] = some env
        ∧ bindDeconstruct ps [Val.seq ys] = some env :=
  receivers_never_same_on_lone_structure ps [Val.seq ys] (loneStructure_lone_seq ys)

/-- List-kind corollary of `receivers_never_same_on_lone_structure`. -/
theorem receivers_never_agree_on_lone_list (ps : List Pat) (ys : List Val) :
    ¬ ∃ env, bindArgs ps [Val.list ys] = some env
        ∧ bindDeconstruct ps [Val.list ys] = some env :=
  receivers_never_same_on_lone_structure ps [Val.list ys] (loneStructure_lone_list ys)

/-- Why the lone-structure theorem is stated over shared SUCCESS: both
receivers can fail identically on a lone structure. Two fixed names against a
lone one-item sequence value fail on both sides (arity 2 vs 1 either way), so
option-level inequality would be a false general claim. -/
example :
    bindArgs [Pat.name "x", Pat.name "y"] [Val.seq [Val.atom 1]]
      = bindDeconstruct [Pat.name "x", Pat.name "y"] [Val.seq [Val.atom 1]] := by
  decide

/-- The lone-collecting disagreement on a lone LIST supply: call binding collects
the one supplied argument (`rest = [[1, 2]]`-style nesting), while
deconstruction opens the lone list and collects its items — never the same
binding. -/
theorem lone_collecting_disagrees_on_lone_list (r : String) (ys : List Val) :
    bindArgs [Pat.collecting r] [Val.list ys]
      ≠ bindDeconstruct [Pat.collecting r] [Val.list ys] := by
  rw [bindArgs_lone_collecting, bindDeconstruct, openLoneStructure_singleList,
      show bindPats [Pat.collecting r] ys = bindArgs [Pat.collecting r] ys from rfl,
      bindArgs_lone_collecting]
  intro he
  have hv : collect [Val.list ys] = collect ys := by
    have := Option.some.inj he
    have hpair := List.cons.inj this
    simpa using congrArg Prod.snd hpair.1
  have hpay : [Val.list ys] = ys := by
    simpa [collect] using hv
  exact list_payload_not_self ys (Val.list ys) hpay (fun w hw => mem_ne_list hw)

/-! ## Canonical-form theorems (general)

The shape-specific checks earlier in this file pin `normalize`/`capture` on
concrete values. The theorems below establish the general canonical-form
story over all values:

* `normalize_idempotent` — `normalize` is a projection onto canonical values;
* `orphanFree_normalize` — canonical values contain no redundant singleton
  sequence boundary anywhere in their tree (no literal-unwritable "orphans";
  exact list values carry no singleton-orphan rule, since `[x]` is
  literal-writable);
* `capture_canonical` / `capture_orphanFree` — capture boundaries only ever
  produce canonical, orphan-free values;
* `collect_normalize_elementwise` — collected list values normalize
  element-wise only: the collected boundary itself is stable;
* `capture_items_of_canonical` — capture after spread is the identity on
  canonical NON-LIST values; spreading a list opens its boundary, so
  re-capture converts it to the canonical capture of its elements
  (`capture_items_of_list`).
-/

/-- Unfolding case split for `normalize` on a sequence value: an empty
normalized payload yields the empty sequence value. -/
theorem normalize_seq_of_list_nil {xs : List Val} (h : normalizeList xs = []) :
    normalize (Val.seq xs) = Val.seq [] := by
  simp only [normalize, h]

/-- Unfolding case split for `normalize` on a sequence value: a singleton
normalized payload collapses the redundant boundary. -/
theorem normalize_seq_of_list_singleton {xs : List Val} {v : Val}
    (h : normalizeList xs = [v]) :
    normalize (Val.seq xs) = v := by
  simp only [normalize, h]

/-- Unfolding case split for `normalize` on a sequence value: a multi-item
normalized payload keeps the boundary intact. -/
theorem normalize_seq_of_list_multi {xs : List Val} {a b : Val} {tl : List Val}
    (h : normalizeList xs = a :: b :: tl) :
    normalize (Val.seq xs) = Val.seq (a :: b :: tl) := by
  simp only [normalize, h]

mutual
  /-- General idempotence: `normalize` is a projection, so normalizing an
  already-normalized value changes nothing. Canonical values are exactly the
  fixed points of `normalize`. -/
  theorem normalize_idempotent : ∀ v : Val, normalize (normalize v) = normalize v
    | .atom _ => rfl
    | .seq xs => by
        have hl := normalizeList_idempotent xs
        cases h : normalizeList xs with
        | nil =>
            rw [normalize_seq_of_list_nil h]
            exact normalize_empty
        | cons v tl =>
            cases tl with
            | nil =>
                rw [normalize_seq_of_list_singleton h]
                rw [h] at hl
                have h2 : ([normalize v] : List Val) = [v] := hl
                simpa using h2
            | cons w tl2 =>
                rw [normalize_seq_of_list_multi h]
                rw [h] at hl
                exact normalize_seq_of_list_multi hl
    | .list xs => by
        have hl := normalizeList_idempotent xs
        rw [normalize_list_exact, normalize_list_exact, hl]
  termination_by v => sizeOf v

  /-- Element-wise idempotence for the mutual payload traversal of
  `normalize_idempotent`. -/
  theorem normalizeList_idempotent : ∀ xs : List Val,
      normalizeList (normalizeList xs) = normalizeList xs
    | [] => rfl
    | x :: xs => by
        show normalize (normalize x) :: normalizeList (normalizeList xs)
            = normalize x :: normalizeList xs
        rw [normalize_idempotent x, normalizeList_idempotent xs]
  termination_by xs => sizeOf xs
end

/-- Collected list values normalize element-wise only: the collect boundary is
already canonical (`normalize (collect xs) = collect (normalizeList xs)`). -/
theorem collect_normalize_elementwise (xs : Supply) :
    normalize (collect xs) = collect (normalizeList xs) := rfl

mutual
  /-- Orphan-freedom: `true` iff no singleton sequence boundary `Val.seq [x]`
  appears anywhere in the value. A singleton sequence boundary is a
  literal-unwritable "orphan" (a stored `(5)` distinct from `5`): `normalize`
  erases such boundaries at every construction/capture site, so no canonical
  value contains one (`orphanFree_normalize`). Exact list values carry NO
  singleton-orphan rule — `[x]` is literal-writable — so only their elements
  are checked. -/
  def orphanFree : Val -> Bool
    | .atom _ => true
    | .seq xs => xs.length != 1 && orphanFreeList xs
    | .list xs => orphanFreeList xs

  /-- List traversal for `orphanFree`. -/
  def orphanFreeList : List Val -> Bool
    | [] => true
    | x :: xs => orphanFree x && orphanFreeList xs
end

example : orphanFree (Val.atom 5) = true := by decide
example : orphanFree (Val.seq []) = true := by decide
example : orphanFree (Val.seq [Val.atom 1]) = false := by decide
example : orphanFree (Val.seq [Val.atom 1, Val.seq [Val.atom 2]]) = false := by decide
example : orphanFree (Val.seq [Val.atom 1, Val.seq []]) = true := by decide
example : orphanFree (Val.list []) = true := by decide
example : orphanFree (Val.list [Val.atom 1]) = true := by decide
example : orphanFree (Val.list [Val.list [Val.atom 1]]) = true := by decide
example : orphanFree (Val.list [Val.seq [Val.atom 1]]) = false := by decide

mutual
  /-- Orphan-freedom of canonical values: normalization never leaves a
  redundant singleton sequence boundary anywhere in the tree. -/
  theorem orphanFree_normalize : ∀ v : Val, orphanFree (normalize v) = true
    | .atom _ => rfl
    | .seq xs => by
        have hl := orphanFreeList_normalizeList xs
        cases h : normalizeList xs with
        | nil =>
            rw [normalize_seq_of_list_nil h]
            rfl
        | cons v tl =>
            cases tl with
            | nil =>
                rw [normalize_seq_of_list_singleton h]
                rw [h] at hl
                have h2 : (orphanFree v && true) = true := hl
                simpa using h2
            | cons w tl2 =>
                rw [normalize_seq_of_list_multi h]
                rw [h] at hl
                have hlen : ((v :: w :: tl2).length != 1) = true := by
                  simp only [List.length_cons, bne_iff_ne, ne_eq]
                  omega
                show ((v :: w :: tl2).length != 1 && orphanFreeList (v :: w :: tl2)) = true
                rw [hlen, hl]
                rfl
    | .list xs => by
        have hl := orphanFreeList_normalizeList xs
        rw [normalize_list_exact]
        show orphanFreeList (normalizeList xs) = true
        exact hl
  termination_by v => sizeOf v

  /-- List form of `orphanFree_normalize` for the mutual payload traversal. -/
  theorem orphanFreeList_normalizeList : ∀ xs : List Val,
      orphanFreeList (normalizeList xs) = true
    | [] => rfl
    | x :: xs => by
        show (orphanFree (normalize x) && orphanFreeList (normalizeList xs)) = true
        rw [orphanFree_normalize x, orphanFreeList_normalizeList xs]
        rfl
  termination_by xs => sizeOf xs
end

/-- Capture canonicity: a captured item supply is already canonical, so capture
is a fixed point of `normalize` (corollary of `normalize_idempotent`, since
`capture xs = normalize (Val.seq xs)`). -/
theorem capture_canonical (xs : Supply) : normalize (capture xs) = capture xs :=
  normalize_idempotent (Val.seq xs)

/-- Capture never mints an orphan: every captured value is orphan-free
(corollary of `orphanFree_normalize`). -/
theorem capture_orphanFree (xs : Supply) : orphanFree (capture xs) = true :=
  orphanFree_normalize (Val.seq xs)

/-- Spread/capture round-trip, restricted to non-list values: on a canonical
value that is not an exact list, re-capturing the item view (the supply an
explicit spread `...` provides) reproduces the value exactly. -/
theorem capture_items_of_canonical (v : Val) (h : normalize v = v)
    (hl : ∀ xs, v ≠ Val.list xs) :
    capture (items v) = v := by
  cases v with
  | atom n => rfl
  | seq xs => exact h
  | list xs => exact absurd rfl (hl xs)

/-- Spread-then-CAPTURE on a list yields the canonical capture of its
elements — never the same list back: `x = A...` re-groups list items into
the sequence world. (Spread-then-COLLECT, by contrast, reproduces the list:
`items_collect`.) -/
theorem capture_items_of_list (xs : Supply) :
    capture (items (Val.list xs)) = capture xs := rfl

/-- Collect/spread/collect collapse: re-collecting a collected value's items
is the identity — the list-side round trip composes (corollary of
`items_collect`). -/
theorem collect_items_collect (xs : Supply) :
    collect (items (collect xs)) = collect xs := rfl

/-! ## Canonical-supply invariant (`canonicalSupply`)

The abstract `Supply` type admits raw non-canonical members; observable
runtime supplies do not. `canonicalSupply` names that invariant, and the laws
below close it under the algebra's operations: the empty supply is canonical,
normalization produces canonical supplies, opening a canonical VALUE yields a
canonical supply, and collecting a canonical supply yields an
already-canonical list. That last law is the precise sense in which `collect`
needs no normalization of its own: `collect` preserves the number, order,
kinds, and boundaries of the supplied values as-is, and canonicality of the
result comes from the input invariant, not from work performed inside
`collect` (the full model's `collectSegment` likewise stores its supply
unchanged).
-/

/-- Element-wise normalization preserves length, so canonicalization never
changes how many items a supply carries. -/
theorem normalizeList_length : ∀ xs : Supply,
    (normalizeList xs).length = xs.length
  | [] => rfl
  | x :: t => by
      show (normalize x :: normalizeList t).length = (x :: t).length
      simp [normalizeList_length t]

/-- The two formulations of the invariant agree: a supply is canonical iff
every member is a `normalize` fixed point. -/
theorem canonicalSupply_iff_forall (xs : Supply) :
    canonicalSupply xs ↔ ∀ v ∈ xs, normalize v = v := by
  induction xs with
  | nil =>
      constructor
      · intro _ v hv
        cases hv
      · intro _
        rfl
  | cons x t ih =>
      constructor
      · intro h v hv
        have h' : normalize x :: normalizeList t = x :: t := h
        have hx : normalize x = x := (List.cons.inj h').1
        have ht : canonicalSupply t := (List.cons.inj h').2
        rcases List.mem_cons.mp hv with hveq | hvt
        · rw [hveq]; exact hx
        · exact (ih.mp ht) v hvt
      · intro h
        have hx : normalize x = x := h x List.mem_cons_self
        have ht : canonicalSupply t :=
          ih.mpr (fun v hv => h v (List.mem_cons_of_mem x hv))
        show normalize x :: normalizeList t = x :: t
        rw [hx, show normalizeList t = t from ht]

theorem canonicalSupply_nil : canonicalSupply [] := rfl

-- Representative invariant checks: empty structures and exact nested lists
-- are canonical, while raw singleton-sequence orphans are not, including when
-- one is nested inside an exact list.
example : canonicalSupply [Val.seq []] := rfl
example : canonicalSupply [Val.list []] := rfl
example : canonicalSupply [Val.list [Val.list [Val.atom 7]]] := rfl
example : ¬ canonicalSupply [Val.seq [Val.atom 7]] := by
  simp [canonicalSupply, normalizeList, normalize]
example : ¬ canonicalSupply [Val.list [Val.seq [Val.atom 7]]] := by
  simp [canonicalSupply, normalizeList, normalize]

/-- Normalization always produces a canonical supply (corollary of
`normalizeList_idempotent`). -/
theorem canonicalSupply_normalizeList (xs : Supply) :
    canonicalSupply (normalizeList xs) :=
  normalizeList_idempotent xs

/-- Collecting a canonical supply is already canonical: collecting binding stores
observable (canonical) values without renormalizing them, and the collected
list is a `normalize` fixed point purely because its INPUT satisfied the
invariant. -/
theorem normalize_collect_of_canonicalSupply {xs : Supply}
    (h : canonicalSupply xs) :
    normalize (collect xs) = collect xs := by
  rw [collect_normalize_elementwise, show normalizeList xs = xs from h]

/-- Membership form of `orphanFreeList` for supply-level reasoning. -/
theorem orphanFreeList_of_forall {xs : Supply}
    (h : ∀ v ∈ xs, orphanFree v = true) : orphanFreeList xs = true := by
  induction xs with
  | nil => rfl
  | cons x t ih =>
      show (orphanFree x && orphanFreeList t) = true
      rw [h x List.mem_cons_self,
        ih (fun v hv => h v (List.mem_cons_of_mem x hv))]
      rfl

/-- Exact collection preserves orphan-freedom: when every supplied value is
orphan-free, the collected list is orphan-free as well — the list boundary
itself carries no orphan rule (`[x]` is literal-writable), so nothing about
`collect` can mint one. -/
theorem collect_orphanFree_of_elements {xs : Supply}
    (h : ∀ v ∈ xs, orphanFree v = true) :
    orphanFree (collect xs) = true := by
  show orphanFreeList xs = true
  exact orphanFreeList_of_forall h

/-- Opening a canonical value yields a canonical supply: the invariant is
closed under `open`, so supplies assembled from spreads of canonical stored
values are canonical without renormalization. (For a canonical sequence value
the stored payload is its own normalization — the singleton-collapse case is
impossible because it would leave an orphan boundary, contradicting
`orphanFree_normalize`.) -/
theorem canonicalSupply_items_of_canonical {v : Val} (h : normalize v = v) :
    canonicalSupply (items v) := by
  cases v with
  | atom n => rfl
  | list xs =>
      have h' : Val.list (normalizeList xs) = Val.list xs := h
      show normalizeList xs = xs
      exact Val.list.inj h'
  | seq xs =>
      show normalizeList xs = xs
      cases hl : normalizeList xs with
      | nil =>
          have h0 := normalize_seq_of_list_nil hl
          rw [h] at h0
          have hx : xs = [] := Val.seq.inj h0
          subst hx
          rfl
      | cons u tl =>
          cases tl with
          | nil =>
              have hu : Val.seq xs = u :=
                h.symm.trans (normalize_seq_of_list_singleton hl)
              have hlen := normalizeList_length xs
              rw [hl] at hlen
              cases xs with
              | nil => simp at hlen
              | cons w t =>
                  cases t with
                  | cons b t2 => simp at hlen
                  | nil =>
                      have hnu : normalize w = u := by
                        have h' : ([normalize w] : List Val) = [u] := hl
                        exact (List.cons.inj h').1
                      have hw : normalize w = Val.seq [w] := hnu.trans hu.symm
                      have ho := orphanFree_normalize w
                      rw [hw] at ho
                      simp [orphanFree, orphanFreeList] at ho
          | cons b tl2 =>
              have hx : Val.seq xs = Val.seq (u :: b :: tl2) :=
                h.symm.trans (normalize_seq_of_list_multi hl)
              exact (Val.seq.inj hx).symm

/-- The invariant composes with the receiver operations end to end: a collecting binding
that collects the spread of a canonical stored value stores a canonical list
(`normalize_collect_of_canonicalSupply` after
`canonicalSupply_items_of_canonical`). -/
theorem normalize_collect_items_of_canonical {v : Val} (h : normalize v = v) :
    normalize (collect (items v)) = collect (items v) :=
  normalize_collect_of_canonicalSupply (canonicalSupply_items_of_canonical h)

end CoreArityAlgebra
