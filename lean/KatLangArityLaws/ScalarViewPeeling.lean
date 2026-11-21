import KatLangArityLaws

open KatLang

/-!
# The scalar views decide from sequence shape (KL-02, November 2026)

Lean's `Result.asInt?` and `Result.asBool?` inspect the normal form of a sequence. In C#,
`Result.ScalarViewTerminal` follows the child of each singleton sequence. `NumberOf` and
`BooleanOf` inspect the resulting terminal. An empty or multi-item sequence or a list rejects
both views immediately. The two general equivalences below cover every Lean `Result`.

DEFINITIONS. `scalarViewTerminalForLaw`, `numberOfForLaw` and `booleanOfForLaw` are LOCAL models
of `ScalarViewTerminal`, `NumberOf` and `BooleanOf`, read from `src/KatLang/Result.cs`. C# has one
`CallReference` class for both of Lean's opaque constructors `callRef` and `argView`; both
decisions give `null` / `none` for it. `singletonWrapForLaw k r` is `r` under `k` redundant
singleton sequence boundaries, and `singletonDepthForLaw r` counts the boundaries the terminal
peels.

RESULTS.

1. The general equivalence: `asInt_eq_numberOf_terminal` and `asBool_eq_booleanOf_terminal`. Each
   view is the C# decision applied to the peeled terminal, with no premise. In iff form:
   `asInt_eq_some_iff`, `asBool_eq_some_iff`, `asInt_eq_none_iff` and `asBool_eq_none_iff`.
2. The rule behind it: peeling keeps the normal form (`normalize_terminal`), and the normal form
   is a number or a Boolean exactly when the terminal is that same number or Boolean
   (`normalize_eq_atom_iff`, `normalize_eq_bool_iff`).
3. Peeling: one singleton boundary is transparent to both views, whatever it holds
   (`asInt_peels_singleton_sequence`, `asBool_peels_singleton_sequence`). The existing
   `asBool_singleton_sequence` is the instance of the second at a Boolean.
4. Rejection at the deciding boundary: an empty or multi-item sequence has neither view,
   whatever its items and however normalizable they are (`asInt_non_singleton_sequence_none`,
   `asBool_non_singleton_sequence_none`). A terminal that is a sequence is never a singleton, and a
   terminal sequence or list rejects both views (`scalar_views_none_of_terminal_sequence`,
   `scalar_views_none_of_terminal_list`).
5. Arbitrary nesting: every value is its terminal under exactly `singletonDepthForLaw` wrappers
   (`wrap_depth_terminal`), and `k` wrappers change neither view (`asInt_wrap`, `asBool_wrap`).
   At every depth, a number reads as itself and a Boolean as itself, and lists, empty and
   multi-item sequences and the wrong-kind leaves have no view (`asInt_wrap_*`, `asBool_wrap_*`).
   Apart from the empty sequence, the `asBool_wrap_*` corollaries are the existing `asBool_*`
   lemmas lifted through `asBool_wrap`.

Lean's `Result.atom` carries an `Int`. The numeric theorem returns that integer unchanged.
C#'s `Result.Atom` carries a `Decimal128`. The loop in `Result.cs` returns the stored terminal
object, and the public views extract its payload. `NumericRepresentativeSelectionTests` checks
the decimal bits, including quantum, signed zero and NaN sign. The `ScalarViews_*` tests in
`NormalizeSharedValueGraphTests` compare both views with full normalization, count sequence
inspections and bound measured allocations. These runtime properties have C# evidence.

EVIDENCE. The views `asInt?` / `asBool?` and `normalize` are total definitions of `KatLang.lean`
that the evaluator calls. Theorems whose statements mention only them are PRODUCTION theorems in
the sense of `KatLangArityLaws.lean`: `normalize_non_singleton_sequence` and every theorem of
§ Leaf and boundary facts of the two views (`asInt_peels_singleton_sequence`,
`asInt_non_singleton_sequence_none`, …). Theorems whose statements mention a helper defined here
(`asInt_eq_numberOf_normalize`, the general equivalence, the nesting laws) are LOCAL theorems
about a model of C# source. No theorem here proves C# code: the agreement of `ScalarViewTerminal`
with `scalarViewTerminalForLaw` is inspection, and the pins named above test it.
-/

namespace KatLang.ScalarViewPeeling

/-! ## The local models of the C# helpers -/

/-- LOCAL model of C# `Result.ScalarViewTerminal`: peel every redundant singleton sequence
wrapper, and stop at the first value that is not a one-item sequence. -/
def scalarViewTerminalForLaw : Result → Result
  | .sequenceValue [r] => scalarViewTerminalForLaw r
  | r => r

/-- LOCAL model of C# `Result.NumberOf`, the numeric decision on a terminal: a number is itself,
and every other kind (string, Boolean, sequence, list, call reference, argument view) is no
number. The terminal is never normalized first. -/
def numberOfForLaw : Result → Option Int
  | .atom n => some n
  | _ => none

/-- LOCAL model of C# `Result.BooleanOf`, the Boolean decision on a terminal: only a Boolean
qualifies. -/
def booleanOfForLaw : Result → Option Bool
  | .bool b => some b
  | _ => none

/-- `r` under `k` redundant singleton sequence boundaries (`(…(r)…)`); the outermost one is
added last. -/
def singletonWrapForLaw : Nat → Result → Result
  | 0, r => r
  | Nat.succ k, r => .sequenceValue [singletonWrapForLaw k r]

/-- The number of singleton sequence boundaries `scalarViewTerminalForLaw` peels. -/
def singletonDepthForLaw : Result → Nat
  | .sequenceValue [r] => singletonDepthForLaw r + 1
  | _ => 0

/-! ## Peeling -/

theorem terminal_singleton (r : Result) :
    scalarViewTerminalForLaw (.sequenceValue [r]) = scalarViewTerminalForLaw r := by
  simp [scalarViewTerminalForLaw]

/-- Peeling leaves a value that is not a one-item sequence unchanged. -/
theorem terminal_of_not_singleton {r : Result} (h : ∀ x, r ≠ .sequenceValue [x]) :
    scalarViewTerminalForLaw r = r := by
  match r with
  | .atom _ | .str _ | .bool _ | .listValue _ | .callRef _ | .argView _ =>
      simp [scalarViewTerminalForLaw]
  | .sequenceValue [] => simp [scalarViewTerminalForLaw]
  | .sequenceValue [x] => exact absurd rfl (h x)
  | .sequenceValue (_ :: _ :: _) => simp [scalarViewTerminalForLaw]

/-- Peeling stops at the first value that is not a one-item sequence: a terminal is never one. -/
theorem terminal_not_singleton : ∀ (r x : Result),
    scalarViewTerminalForLaw r ≠ .sequenceValue [x]
  | .sequenceValue [r], x => by
      rw [terminal_singleton]
      exact terminal_not_singleton r x
  | .atom _, _ | .str _, _ | .bool _, _ | .listValue _, _ | .callRef _, _ | .argView _, _ => by
      simp [scalarViewTerminalForLaw]
  | .sequenceValue [], _ => by simp [scalarViewTerminalForLaw]
  | .sequenceValue (_ :: _ :: _), _ => by simp [scalarViewTerminalForLaw]
termination_by r => sizeOf r

/-- A terminal is its own terminal. -/
theorem terminal_idempotent (r : Result) :
    scalarViewTerminalForLaw (scalarViewTerminalForLaw r) = scalarViewTerminalForLaw r :=
  terminal_of_not_singleton (terminal_not_singleton r)

/-- The empty item list is not a singleton. Stated as a term, as is the next lemma, so that the
principal theorems below need no `Classical.choice` (§ Axiom audit). -/
theorem nil_length_ne_one : ([] : List Result).length ≠ 1 := Nat.zero_ne_one

/-- Two or more items are not a singleton. -/
theorem multi_item_length_ne_one (a b : Result) (rest : List Result) :
    (a :: b :: rest).length ≠ 1 :=
  fun h => Nat.succ_ne_zero _ (Nat.succ.inj h)

/-- A terminal that is a sequence is empty or has at least two items. -/
theorem terminal_sequence_length {r : Result} {rs : List Result}
    (h : scalarViewTerminalForLaw r = .sequenceValue rs) : rs.length ≠ 1 := by
  match rs with
  | [] => exact nil_length_ne_one
  | [x] => exact absurd h (terminal_not_singleton r x)
  | a :: b :: rest => exact multi_item_length_ne_one a b rest

/-! ## Arbitrary nesting -/

/-- `k` wrappers peel away: the terminal of `(…(r)…)` is the terminal of `r`. -/
theorem terminal_wrap (k : Nat) (r : Result) :
    scalarViewTerminalForLaw (singletonWrapForLaw k r) = scalarViewTerminalForLaw r := by
  induction k with
  | zero => rfl
  | succ k ih =>
      show scalarViewTerminalForLaw (.sequenceValue [singletonWrapForLaw k r]) = _
      rw [terminal_singleton, ih]

/-- Every value is its terminal under exactly `singletonDepthForLaw` singleton boundaries. -/
theorem wrap_depth_terminal : ∀ r : Result,
    singletonWrapForLaw (singletonDepthForLaw r) (scalarViewTerminalForLaw r) = r
  | .sequenceValue [r] => by
      have ih := wrap_depth_terminal r
      simp only [singletonDepthForLaw, terminal_singleton, singletonWrapForLaw, ih]
  | .atom _ | .str _ | .bool _ | .listValue _ | .callRef _ | .argView _ => by
      simp [singletonDepthForLaw, scalarViewTerminalForLaw, singletonWrapForLaw]
  | .sequenceValue [] => by
      simp [singletonDepthForLaw, scalarViewTerminalForLaw, singletonWrapForLaw]
  | .sequenceValue (_ :: _ :: _) => by
      simp [singletonDepthForLaw, scalarViewTerminalForLaw, singletonWrapForLaw]
termination_by r => sizeOf r

/-! ## The terminal and the normal form -/

/-- Normalization keeps an empty or multi-item sequence's boundary and item count while
normalizing each child. -/
theorem normalize_non_singleton_sequence {rs : List Result} (h : rs.length ≠ 1) :
    Result.normalize (.sequenceValue rs) = .sequenceValue (rs.map Result.normalize) := by
  match rs, h with
  | [], _ => simp [Result.normalize]
  | _ :: _ :: _, _ => simp [Result.normalize]

/-- Peeling never changes the normal form: a value and its terminal normalize alike. -/
theorem normalize_terminal : ∀ r : Result,
    (scalarViewTerminalForLaw r).normalize = r.normalize
  | .sequenceValue [r] => by
      rw [terminal_singleton, normalize_sequenceValue_singleton]
      exact normalize_terminal r
  | .atom _ | .str _ | .bool _ | .listValue _ | .callRef _ | .argView _ => by
      simp [scalarViewTerminalForLaw]
  | .sequenceValue [] => by simp [scalarViewTerminalForLaw]
  | .sequenceValue (_ :: _ :: _) => by simp [scalarViewTerminalForLaw]
termination_by r => sizeOf r

/-- On a value that is not a singleton sequence (every terminal), `normalize` keeps the
constructor, so it is a number exactly when the value is that number. -/
theorem normalize_eq_atom_iff_of_not_singleton {t : Result} (ht : ∀ x, t ≠ .sequenceValue [x])
    (n : Int) : t.normalize = .atom n ↔ t = .atom n := by
  match t with
  | .atom _ | .str _ | .bool _ | .listValue _ | .callRef _ | .argView _ =>
      simp [Result.normalize]
  | .sequenceValue [x] => exact absurd rfl (ht x)
  | .sequenceValue [] => simp [Result.normalize]
  | .sequenceValue (_ :: _ :: _) => simp [Result.normalize]

/-- The Boolean companion of `normalize_eq_atom_iff_of_not_singleton`. -/
theorem normalize_eq_bool_iff_of_not_singleton {t : Result} (ht : ∀ x, t ≠ .sequenceValue [x])
    (b : Bool) : t.normalize = .bool b ↔ t = .bool b := by
  match t with
  | .atom _ | .str _ | .bool _ | .listValue _ | .callRef _ | .argView _ =>
      simp [Result.normalize]
  | .sequenceValue [x] => exact absurd rfl (ht x)
  | .sequenceValue [] => simp [Result.normalize]
  | .sequenceValue (_ :: _ :: _) => simp [Result.normalize]

/-- THE RULE OF `ScalarViewTerminal`: a value normalizes to a number exactly when peeling
reaches that same number. -/
theorem normalize_eq_atom_iff (r : Result) (n : Int) :
    r.normalize = .atom n ↔ scalarViewTerminalForLaw r = .atom n := by
  rw [← normalize_terminal r]
  exact normalize_eq_atom_iff_of_not_singleton (terminal_not_singleton r) n

/-- … and to a Boolean exactly when peeling reaches that same Boolean. -/
theorem normalize_eq_bool_iff (r : Result) (b : Bool) :
    r.normalize = .bool b ↔ scalarViewTerminalForLaw r = .bool b := by
  rw [← normalize_terminal r]
  exact normalize_eq_bool_iff_of_not_singleton (terminal_not_singleton r) b

/-! ## The views read the normal form -/

/-- `asInt?` is the numeric decision on the normal form for every value kind. Normalizing a
list can change its elements, but preserves its list constructor. -/
theorem asInt_eq_numberOf_normalize (r : Result) :
    r.asInt? = numberOfForLaw r.normalize := by
  cases r <;> simp [Result.asInt?, Result.normalize, numberOfForLaw]
  case sequenceValue rs => split <;> simp_all

/-- `asBool?` is the Boolean decision on the normal form, for every value kind. -/
theorem asBool_eq_booleanOf_normalize (r : Result) :
    r.asBool? = booleanOfForLaw r.normalize := by
  cases r <;> simp [Result.asBool?, Result.normalize, booleanOfForLaw]
  case sequenceValue rs => split <;> simp_all

/-! ## Leaf and boundary facts of the two views (production)

The numeric counterparts of the `asBool_*` lemmas of `KatLangArityLaws.lean` (`asInt_bool_none`
is already there), the Boolean view of the two opaque constructors and of the empty sequence, and
the peeling and rejection facts of both views. The four opaque-constructor facts restate, one view
each, parts of `reference_is_opaque` (`CallReference.lean`) and `view_is_opaque`
(`ArgumentView.lean`), which this module does not import. -/

theorem asInt_atom (n : Int) : Result.asInt? (Result.atom n) = some n := rfl

theorem asInt_str_none (s : String) : Result.asInt? (Result.str s) = none := rfl

/-- Lists never coerce to numbers, not even `[5]`. -/
theorem asInt_list_none (rs : List Result) : Result.asInt? (Result.listValue rs) = none := rfl

theorem asInt_callRef_none (a : Nat) : Result.asInt? (Result.callRef a) = none := rfl

theorem asInt_argView_none (a : Nat) : Result.asInt? (Result.argView a) = none := rfl

theorem asBool_callRef_none (a : Nat) : Result.asBool? (Result.callRef a) = none := rfl

theorem asBool_argView_none (a : Nat) : Result.asBool? (Result.argView a) = none := rfl

/-- One redundant singleton sequence boundary is transparent to the numeric view, whatever it
holds. -/
theorem asInt_peels_singleton_sequence (r : Result) :
    Result.asInt? (Result.sequenceValue [r]) = Result.asInt? r := by
  rw [asInt_eq_numberOf_normalize, asInt_eq_numberOf_normalize,
    normalize_sequenceValue_singleton]

/-- One redundant singleton sequence boundary is transparent to the Boolean view, whatever it
holds. This generalizes `asBool_singleton_sequence` from a Boolean to every value. -/
theorem asBool_peels_singleton_sequence (r : Result) :
    Result.asBool? (Result.sequenceValue [r]) = Result.asBool? r := by
  rw [asBool_eq_booleanOf_normalize, asBool_eq_booleanOf_normalize,
    normalize_sequenceValue_singleton]

/-- An empty or multi-item sequence is no number, whatever its items: the numeric view does no
flattening. The items are never normalized into the answer. -/
theorem asInt_non_singleton_sequence_none {rs : List Result} (h : rs.length ≠ 1) :
    Result.asInt? (Result.sequenceValue rs) = none := by
  rw [asInt_eq_numberOf_normalize, normalize_non_singleton_sequence h]
  rfl

/-- An empty or multi-item sequence is no Boolean, whatever its items. -/
theorem asBool_non_singleton_sequence_none {rs : List Result} (h : rs.length ≠ 1) :
    Result.asBool? (Result.sequenceValue rs) = none := by
  rw [asBool_eq_booleanOf_normalize, normalize_non_singleton_sequence h]
  rfl

theorem asInt_empty_sequence_none : Result.asInt? (Result.sequenceValue []) = none :=
  asInt_non_singleton_sequence_none nil_length_ne_one

theorem asBool_empty_sequence_none : Result.asBool? (Result.sequenceValue []) = none :=
  asBool_non_singleton_sequence_none nil_length_ne_one

/-- The numeric counterpart of `asBool_multi_item_sequence_none`. -/
theorem asInt_multi_item_sequence_none (a b : Result) (rest : List Result) :
    Result.asInt? (Result.sequenceValue (a :: b :: rest)) = none :=
  asInt_non_singleton_sequence_none (multi_item_length_ne_one a b rest)

/-! ## The general equivalence -/

/-- THE NUMERIC VIEW DECIDES FROM SEQUENCE SHAPE: for every value, `asInt?` is the C# numeric
decision on the peeled terminal. The proof splits on the value's shape, one leaf or boundary fact
per case and one peeled boundary per recursive step. -/
theorem asInt_eq_numberOf_terminal : ∀ r : Result,
    r.asInt? = numberOfForLaw (scalarViewTerminalForLaw r)
  | .sequenceValue [r] => by
      rw [asInt_peels_singleton_sequence, terminal_singleton]
      exact asInt_eq_numberOf_terminal r
  | .atom n => asInt_atom n
  | .str s => asInt_str_none s
  | .bool b => asInt_bool_none b
  | .listValue rs => asInt_list_none rs
  | .callRef a => asInt_callRef_none a
  | .argView a => asInt_argView_none a
  | .sequenceValue [] => asInt_empty_sequence_none
  | .sequenceValue (a :: b :: rest) => asInt_multi_item_sequence_none a b rest
termination_by r => sizeOf r

/-- THE BOOLEAN VIEW DECIDES FROM SEQUENCE SHAPE: for every value, `asBool?` is the C# Boolean
decision on the peeled terminal. The Boolean, number, string, list and multi-item cases are the
existing `asBool_*` lemmas of `KatLangArityLaws.lean`; the empty sequence and the two opaque
constructors use the lemmas above. -/
theorem asBool_eq_booleanOf_terminal : ∀ r : Result,
    r.asBool? = booleanOfForLaw (scalarViewTerminalForLaw r)
  | .sequenceValue [r] => by
      rw [asBool_peels_singleton_sequence, terminal_singleton]
      exact asBool_eq_booleanOf_terminal r
  | .bool b => asBool_bool b
  | .atom n => asBool_atom_none n
  | .str s => asBool_str_none s
  | .listValue rs => asBool_list_none rs
  | .callRef a => asBool_callRef_none a
  | .argView a => asBool_argView_none a
  | .sequenceValue [] => asBool_empty_sequence_none
  | .sequenceValue (a :: b :: rest) => asBool_multi_item_sequence_none a b rest
termination_by r => sizeOf r

/-- A value is the number `n` exactly when peeling reaches `n`: the payload is returned
unchanged. -/
theorem asInt_eq_some_iff (r : Result) (n : Int) :
    r.asInt? = some n ↔ scalarViewTerminalForLaw r = .atom n := by
  rw [asInt_eq_numberOf_terminal]
  constructor
  · intro h
    revert h
    cases scalarViewTerminalForLaw r <;> simp [numberOfForLaw]
  · intro h
    rw [h]
    rfl

/-- A value is the Boolean `b` exactly when peeling reaches `b`. -/
theorem asBool_eq_some_iff (r : Result) (b : Bool) :
    r.asBool? = some b ↔ scalarViewTerminalForLaw r = .bool b := by
  rw [asBool_eq_booleanOf_terminal]
  constructor
  · intro h
    revert h
    cases scalarViewTerminalForLaw r <;> simp [booleanOfForLaw]
  · intro h
    rw [h]
    rfl

/-- A value has no numeric view exactly when its terminal is not a number. -/
theorem asInt_eq_none_iff (r : Result) :
    r.asInt? = none ↔ ∀ n, scalarViewTerminalForLaw r ≠ .atom n := by
  rw [asInt_eq_numberOf_terminal]
  cases scalarViewTerminalForLaw r <;> simp [numberOfForLaw]

/-- A value has no Boolean view exactly when its terminal is not a Boolean. -/
theorem asBool_eq_none_iff (r : Result) :
    r.asBool? = none ↔ ∀ b, scalarViewTerminalForLaw r ≠ .bool b := by
  rw [asBool_eq_booleanOf_terminal]
  cases scalarViewTerminalForLaw r <;> simp [booleanOfForLaw]

/-- REJECTION AT THE DECIDING SEQUENCE: when peeling stops at a sequence, that sequence is empty or
has at least two items, and the value has neither view. The statement has no premise on the
items. -/
theorem scalar_views_none_of_terminal_sequence {r : Result} {rs : List Result}
    (h : scalarViewTerminalForLaw r = .sequenceValue rs) :
    rs.length ≠ 1 ∧ r.asInt? = none ∧ r.asBool? = none := by
  refine ⟨terminal_sequence_length h, ?_, ?_⟩
  · rw [asInt_eq_numberOf_terminal, h]; rfl
  · rw [asBool_eq_booleanOf_terminal, h]; rfl

/-- REJECTION AT A LIST: when peeling stops at a list, the value has neither view, whatever the
list holds (`[5]` and `[true]` included). -/
theorem scalar_views_none_of_terminal_list {r : Result} {rs : List Result}
    (h : scalarViewTerminalForLaw r = .listValue rs) :
    r.asInt? = none ∧ r.asBool? = none := by
  refine ⟨?_, ?_⟩
  · rw [asInt_eq_numberOf_terminal, h]; rfl
  · rw [asBool_eq_booleanOf_terminal, h]; rfl

/-! ## Every depth of nesting -/

/-- Any number of redundant singleton boundaries is transparent to the numeric view. -/
theorem asInt_wrap (k : Nat) (r : Result) :
    (singletonWrapForLaw k r).asInt? = r.asInt? := by
  induction k with
  | zero => rfl
  | succ k ih =>
      show Result.asInt? (.sequenceValue [singletonWrapForLaw k r]) = _
      rw [asInt_peels_singleton_sequence, ih]

/-- Any number of redundant singleton boundaries is transparent to the Boolean view. -/
theorem asBool_wrap (k : Nat) (r : Result) :
    (singletonWrapForLaw k r).asBool? = r.asBool? := by
  induction k with
  | zero => rfl
  | succ k ih =>
      show Result.asBool? (.sequenceValue [singletonWrapForLaw k r]) = _
      rw [asBool_peels_singleton_sequence, ih]

theorem asInt_wrap_atom (k : Nat) (n : Int) :
    (singletonWrapForLaw k (.atom n)).asInt? = some n := by
  rw [asInt_wrap]; exact asInt_atom n

theorem asInt_wrap_str_none (k : Nat) (s : String) :
    (singletonWrapForLaw k (.str s)).asInt? = none := by
  rw [asInt_wrap]; exact asInt_str_none s

theorem asInt_wrap_bool_none (k : Nat) (b : Bool) :
    (singletonWrapForLaw k (.bool b)).asInt? = none := by
  rw [asInt_wrap]; exact asInt_bool_none b

theorem asInt_wrap_list_none (k : Nat) (rs : List Result) :
    (singletonWrapForLaw k (.listValue rs)).asInt? = none := by
  rw [asInt_wrap]; exact asInt_list_none rs

theorem asInt_wrap_non_singleton_sequence_none (k : Nat) {rs : List Result} (h : rs.length ≠ 1) :
    (singletonWrapForLaw k (.sequenceValue rs)).asInt? = none := by
  rw [asInt_wrap]; exact asInt_non_singleton_sequence_none h

theorem asBool_wrap_bool (k : Nat) (b : Bool) :
    (singletonWrapForLaw k (.bool b)).asBool? = some b := by
  rw [asBool_wrap]; exact asBool_bool b

theorem asBool_wrap_atom_none (k : Nat) (n : Int) :
    (singletonWrapForLaw k (.atom n)).asBool? = none := by
  rw [asBool_wrap]; exact asBool_atom_none n

theorem asBool_wrap_str_none (k : Nat) (s : String) :
    (singletonWrapForLaw k (.str s)).asBool? = none := by
  rw [asBool_wrap]; exact asBool_str_none s

theorem asBool_wrap_list_none (k : Nat) (rs : List Result) :
    (singletonWrapForLaw k (.listValue rs)).asBool? = none := by
  rw [asBool_wrap]; exact asBool_list_none rs

theorem asBool_wrap_empty_sequence_none (k : Nat) :
    (singletonWrapForLaw k (.sequenceValue [])).asBool? = none := by
  rw [asBool_wrap]; exact asBool_empty_sequence_none

theorem asBool_wrap_multi_item_sequence_none (k : Nat) (a b : Result) (rest : List Result) :
    (singletonWrapForLaw k (.sequenceValue (a :: b :: rest))).asBool? = none := by
  rw [asBool_wrap]; exact asBool_multi_item_sequence_none a b rest

/-! ## Examples

These values are host-built: the parser erases a redundant written group, so source never
spells a singleton boundary. -/

/-- The existing `asBool_singleton_sequence` is the Boolean instance of the general peel. -/
example (b : Bool) : Result.asBool? (Result.sequenceValue [Result.bool b]) = some b :=
  (asBool_peels_singleton_sequence (.bool b)).trans (asBool_bool b)

/-- Three singleton boundaries around `7` read as `7`. -/
example : Result.asInt? (singletonWrapForLaw 3 (.atom 7)) = some 7 := asInt_wrap_atom 3 7

/-- Two singleton boundaries around the pair `(7, 8)` read as no number, although each item is
one. -/
example : Result.asInt? (singletonWrapForLaw 2 (.sequenceValue [.atom 7, .atom 8])) = none :=
  asInt_wrap_non_singleton_sequence_none 2 (multi_item_length_ne_one _ _ _)

/-- Two singleton boundaries around `[true]` have no truth value: the list boundary decides, not
its one Boolean. -/
example : Result.asBool? (singletonWrapForLaw 2 (.listValue [.bool true])) = none :=
  asBool_wrap_list_none 2 [.bool true]

/-- Two singleton boundaries around the empty sequence `()` have no truth value. -/
example : Result.asBool? (singletonWrapForLaw 2 (.sequenceValue [])) = none :=
  asBool_wrap_empty_sequence_none 2

end KatLang.ScalarViewPeeling

/-! ## Axiom audit

The principal theorems use no `sorry` and no `Classical.choice`. -/

/-- info: 'KatLang.ScalarViewPeeling.asInt_eq_numberOf_terminal' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms KatLang.ScalarViewPeeling.asInt_eq_numberOf_terminal

/-- info: 'KatLang.ScalarViewPeeling.asBool_eq_booleanOf_terminal' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms KatLang.ScalarViewPeeling.asBool_eq_booleanOf_terminal

/-- info: 'KatLang.ScalarViewPeeling.normalize_eq_atom_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms KatLang.ScalarViewPeeling.normalize_eq_atom_iff

/-- info: 'KatLang.ScalarViewPeeling.normalize_eq_bool_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms KatLang.ScalarViewPeeling.normalize_eq_bool_iff

/-- info: 'KatLang.ScalarViewPeeling.wrap_depth_terminal' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms KatLang.ScalarViewPeeling.wrap_depth_terminal

/-- info: 'KatLang.ScalarViewPeeling.scalar_views_none_of_terminal_sequence' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms KatLang.ScalarViewPeeling.scalar_views_none_of_terminal_sequence

/-- info: 'KatLang.ScalarViewPeeling.scalar_views_none_of_terminal_list' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms KatLang.ScalarViewPeeling.scalar_views_none_of_terminal_list
