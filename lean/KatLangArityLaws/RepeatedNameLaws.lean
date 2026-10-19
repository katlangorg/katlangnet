import KatLangArityLaws.BinderCorrespondence
import KatLangArityLaws.NeedControl

open KatLang KatLang.BinderTrace

/-!
# Repeated-name permutation and representative laws (R4 / Q-28, S5, October 2026)

R3 proved the production binder's per-occurrence repeated-name order and verdict
(`KatLangArityLaws/BinderTrace.lean`: `repeated_name_binding`, `repeatedVerdict`,
`traced_repeated_failure_points`). This module proves the Q-28 owner follow-up's
PERMUTATION and REPRESENTATIVE laws (AGENTS.md, Q-28, 2026-10-07) on an explicit domain, and
connects them to that same production traversal.

THE DOMAIN. A REPEATED NAME's contributions are a nonempty finite list of STABLE COMPLETED
observations (`Contribution`): the address the binder would bind, the contribution's complete
counted VALUE (`CountedResult`, value AND emitted count) and its independently available
CALLABLE identity (`Option Algorithm`). The laws are about such observations, not about
arbitrary expressions: moving a stateful or failing expression changes the work performed and
which failure is reached, and NO law here says that. Permuting one name's contributions is not
permuting a call's unrelated parameter positions either.

THE EQUALITY LAWS THE PROOFS USE, and where they come from:

* counted-value equality `==` on `CountedResult` is `=` — `Result.beq` is structural and total
  (S5; formerly an opaque derived instance), and `LawfulBEq Result` is proved below, so the
  count is part of every comparison (`counted_beq_iff`);
* callable identity `sameRepeatedCallableIdentity` is REFLEXIVE and SYMMETRIC for every
  algorithm (`same_identity_refl`, `same_identity_symm`) and TRANSITIVE on the stated domain
  of equal `parentProfile` (`same_identity_trans`): builtins, parentless algorithms and algorithms whose
  parent chains have the same declaration-id presence profile. Outside that domain the
  anonymous-declaration fallback compares opaque `reprStr` strings, and transitivity across a
  MIXED profile (an identified chain, an anonymous one, an identified one) is NOT proved here —
  the premise is explicit wherever it is used (`CallableTransOn`). S6a
  (`CallableIdentityDomain.lean`) proves transitivity whenever no compared level is decided by
  such a mixed fallback, and full transitivity under one explicit printer residual.

THE OPTIONAL-CALLABLE TRAP. Compatibility of two OPTIONAL callable contributions is not
transitive: a value-only contribution is compatible with each of two different callable
identities that conflict with each other. The binder therefore keeps the RICHER
representative: an intervening value-only contribution can never hide the conflict
(`retain_value_only_cannot_hide_a_conflict`, and the negative control `retainKeepFirst` in
`RepeatedNameGuards.lean`, which forgets the richer contribution and accepts the conflict).

RESULTS (for `retain`, the representative fold, proved to be the production traversal):

1. success ⇔ every pair of contributions has equal counted values and every two PRESENT
   callable identities agree (`retain_ok_iff_compatible`);
2. satisfiability is permutation invariant, incompatible combinations included
   (`retain_satisfiable_perm`);
3. the retained contribution is one of the supplied contributions — no synthesized
   value/callable mixture (`retain_mem`);
4. it has a callable identity iff some contribution has (`retain_callable_isSome_iff`);
5. for a fixed written order it is the FIRST among the richest contributions: the first with a
   callable identity if there is one, otherwise the first (`retain_first_richest`);
6. across permutations the retained VALUE (with its count), callable availability and callable
   identity are preserved; the retained ADDRESS and representation need not be
   (`retain_perm_preserves_observation`);
7. the production traversal computes it: over a flat level of name patterns with stable
   capabilities, the production binder (`NeedBinder.bindSources`, hence `bindNeedPatterns`)
   returns exactly the pure fold `flatBind`, and each name's binding is that name's `retain`
   over its own occurrences in written order (`flat_level_is_flatBind`,
   `flatBind_binding_is_retain`, `production_flat_binding_is_retain`).

FAILURE ORDER is not permutation invariant and no law here says it is: which conflict a fixed
order reaches first is R3's schedule (`traced_repeated_failure_points`), and
`CoreTests.ModelC.mixedRepeatedConflicts` keeps the witness that permuting contributions whose
VALUE computations all succeed can turn a callable-identity incompatibility into a counted-value
one. NUMERIC REPRESENTATION: Lean numbers are `Int`, so "retains the original representative" is
results 3 and 5 (an original contribution by address); Decimal128 representation (`1.5` versus
`1.50`, signed zero, NaN, quantum) is C# evidence (`NumericRepresentativeSelectionTests`).

THE LIFTING BOUNDARY (S5). Result 7 is proved here for flat levels of name patterns (fixed and
repeated names, no literal, structural pattern, collector or META capture). For nested structural
patterns the same `bindName` step runs at every depth (R3's schedule), but the occurrences there
bind FRESH ready cells allocated by the run, so a nested contribution is an allocated cell, not
a supplied one. S6a (October 2026) closes that boundary in `NestedRepeatedNames.lean`: the fold
law for validated nested and mixed heads, with fresh-cell provenance, and a production instance
of the stability premise for the binder channels the evaluator passes (`NeedChannels.shell`,
`shell_model_caps`) on completed and Ready cells; `CallableIdentityDomain.lean` widens the
transitivity domain below. Repeated collecting names and repeated META binders are invalid
signatures.
-/

namespace KatLang.RepeatedNameLaws

/-! ## Counted-value equality is equality -/

mutual
  theorem result_beq_refl : ∀ r : Result, Result.beq r r = true
    | .atom _ => by simp [Result.beq]
    | .str _ => by simp [Result.beq]
    | .bool _ => by simp [Result.beq]
    | .sequenceValue xs => by simp only [Result.beq]; exact result_beqList_refl xs
    | .listValue xs => by simp only [Result.beq]; exact result_beqList_refl xs
    | .callRef _ => by simp [Result.beq]
    | .argView _ => by simp [Result.beq]

  theorem result_beqList_refl : ∀ xs : List Result, Result.beqList xs xs = true
    | [] => by simp [Result.beqList]
    | x :: xs => by
        simp only [Result.beqList, result_beq_refl x, result_beqList_refl xs, Bool.and_self]
end

mutual
  theorem result_eq_of_beq : ∀ a b : Result, Result.beq a b = true → a = b
    | .atom x, b, h => by cases b <;> simp_all [Result.beq]
    | .str x, b, h => by cases b <;> simp_all [Result.beq]
    | .bool x, b, h => by cases b <;> simp_all [Result.beq]
    | .callRef x, b, h => by cases b <;> simp_all [Result.beq]
    | .argView x, b, h => by cases b <;> simp_all [Result.beq]
    | .sequenceValue xs, b, h => by
        cases b with
        | sequenceValue ys =>
            rw [result_eqList_of_beq xs ys (by simpa only [Result.beq] using h)]
        | _ => simp [Result.beq] at h
    | .listValue xs, b, h => by
        cases b with
        | listValue ys =>
            rw [result_eqList_of_beq xs ys (by simpa only [Result.beq] using h)]
        | _ => simp [Result.beq] at h

  theorem result_eqList_of_beq : ∀ a b : List Result, Result.beqList a b = true → a = b
    | [], [], _ => rfl
    | [], _ :: _, h => by simp [Result.beqList] at h
    | _ :: _, [], h => by simp [Result.beqList] at h
    | x :: xs, y :: ys, h => by
        simp only [Result.beqList, Bool.and_eq_true] at h
        rw [result_eq_of_beq x y h.1, result_eqList_of_beq xs ys h.2]
end

instance : LawfulBEq Result where
  eq_of_beq {a b} h := result_eq_of_beq a b h
  rfl {a} := result_beq_refl a

/-- THE COUNTED COMPARISON IS EQUALITY, value and emitted count together: two counted results
    compare equal under the binder's `==` exactly when they are equal. -/
theorem counted_beq_iff (a b : CountedResult) : (a == b) = true ↔ a = b := beq_iff_eq

/-- Equal displayed values with different emitted counts are UNEQUAL contributions. -/
theorem counted_beq_needs_equal_counts (v : Result) (m n : Nat) (h : m ≠ n) :
    ((v, m) == (v, n)) = false := by
  simp [h]

/-! ## Callable identity: the total helpers and their laws -/

/-- The former `partial` body of `sameDeclaringScope`, accessor for accessor, is the defining
    equation of the total definition: the function is unchanged (the recursion is structural
    over a finite chain, so this equation determines it). -/
theorem same_declaring_scope_equation (left right : ScopeCtx) :
    sameDeclaringScope left right =
      match left.declarationId, right.declarationId with
      | some a, some b => a == b && left.params == right.params &&
          match left.parent, right.parent with
          | none, none => true
          | some p, some q => sameDeclaringScope p q
          | _, _ => false
      | _, _ => reprStr left.declaration == reprStr right.declaration := by
  cases left with
  | mk lp lps _ _ _ _ _ lid =>
    cases right with
    | mk rp rps _ _ _ _ _ rid =>
      cases lid <;> cases rid <;> cases lp <;> cases rp <;>
        simp [sameDeclaringScope, ScopeCtx.declarationId, ScopeCtx.params, ScopeCtx.parent]

/-- The former `partial` body of `compatibleActivations` is the total definition's equation. -/
theorem compatible_activations_equation (required actual : Option ScopeCtx) :
    compatibleActivations required actual =
      match required, actual with
      | none, none => true
      | some r, some a =>
          (r.activation.isNone || r.activation == a.activation) &&
            compatibleActivations r.parent a.parent
      | _, _ => false := by
  cases required with
  | none => cases actual <;> simp [compatibleActivations]
  | some r =>
    cases actual with
    | none => simp [compatibleActivations]
    | some a =>
      cases r; cases a
      simp [compatibleActivations, ScopeCtx.activation, ScopeCtx.parent]

/-! ### The identity components are lawful -/

theorem property_identity_eq_of_beq : ∀ a b : PropertyIdentity, (a == b) = true → a = b := by
  intro a b h; cases a <;> cases b <;> simp_all [BEq.beq, instBEqPropertyIdentity.beq]

theorem property_identity_beq_refl : ∀ a : PropertyIdentity, (a == a) = true := by
  intro a; cases a <;> simp [BEq.beq, instBEqPropertyIdentity.beq]

instance : LawfulBEq PropertyIdentity where
  eq_of_beq {a b} h := property_identity_eq_of_beq a b h
  rfl {a} := property_identity_beq_refl a

theorem builtin_eq_of_beq : ∀ a b : Builtin, (a == b) = true → a = b := by
  intro a b h; cases a <;> cases b <;> first | rfl | exact absurd h (by decide)

theorem builtin_beq_refl : ∀ a : Builtin, (a == a) = true := by
  intro a; cases a <;> decide

instance : LawfulBEq Builtin where
  eq_of_beq {a b} h := builtin_eq_of_beq a b h
  rfl {a} := builtin_beq_refl a

theorem beq_comm_of_lawful {α : Type} [BEq α] [LawfulBEq α] (a b : α) : (a == b) = (b == a) := by
  cases h : (a == b) <;> cases h' : (b == a) <;> simp_all

/-! ### `sameDeclaringScope`: reflexive, symmetric, transitive on equal id profiles -/

theorem same_declaring_scope_refl : ∀ s : ScopeCtx, sameDeclaringScope s s = true
  | .mk p _ _ _ _ _ _ (some _) => by
      cases p with
      | none => simp [sameDeclaringScope]
      | some q => simp [sameDeclaringScope, same_declaring_scope_refl q]
  | .mk p _ _ _ _ _ _ none => by cases p <;> simp [sameDeclaringScope]

theorem same_declaring_scope_symm : ∀ l r : ScopeCtx, sameDeclaringScope l r = sameDeclaringScope r l
  | .mk lp lps _ _ _ _ _ (some a), .mk rp rps _ _ _ _ _ (some b) => by
      rcases lp with _ | p <;> rcases rp with _ | q
      · simp only [sameDeclaringScope]; rw [beq_comm_of_lawful a b, beq_comm_of_lawful lps rps]
      · simp [sameDeclaringScope]
      · simp [sameDeclaringScope]
      · simp only [sameDeclaringScope]
        rw [beq_comm_of_lawful a b, beq_comm_of_lawful lps rps, same_declaring_scope_symm p q]
  | .mk lp _ _ _ _ _ _ none, .mk rp _ _ _ _ _ _ rid => by
      rcases lp with _ | p <;> rcases rp with _ | q <;> rcases rid with _ | b <;>
        simp only [sameDeclaringScope] <;> exact beq_comm_of_lawful _ _
  | .mk lp _ _ _ _ _ _ (some a), .mk rp _ _ _ _ _ _ none => by
      rcases lp with _ | p <;> rcases rp with _ | q <;>
        simp only [sameDeclaringScope] <;> exact beq_comm_of_lawful _ _

/-- The DECLARATION-ID PRESENCE PROFILE of a scope chain: whether each level, innermost first,
    carries a declaration identity. `sameDeclaringScope` compares two levels structurally when
    both carry one and falls back to comparing printed declarations otherwise. -/
def idProfile : ScopeCtx → List Bool
  | .mk none _ _ _ _ _ _ id => [id.isSome]
  | .mk (some p) _ _ _ _ _ _ id => id.isSome :: idProfile p

/-- TRANSITIVITY of declaring-scope sameness on chains with the SAME id-presence profile. On
    such chains every compared level is either identified in all three (a structural
    comparison) or anonymous in all three (equality of printed declarations). A MIXED profile
    is not covered: there the fallback compares opaque `reprStr` strings of differently shaped
    levels, and no kernel fact relates them. -/
theorem same_declaring_scope_trans : ∀ x y z : ScopeCtx,
    idProfile x = idProfile y → idProfile y = idProfile z →
    sameDeclaringScope x y = true → sameDeclaringScope y z = true → sameDeclaringScope x z = true
  | .mk xp xps _ _ _ _ _ xid, .mk yp yps _ _ _ _ _ yid, .mk zp zps _ _ _ _ _ zid => by
      intro hxy hyz h1 h2
      rcases xid with _ | a <;> rcases yid with _ | b <;> rcases zid with _ | c <;>
        rcases xp with _ | p <;> rcases yp with _ | q <;> rcases zp with _ | r <;>
        simp only [idProfile, List.cons.injEq, Option.isSome_some, Option.isSome_none,
          Bool.false_eq_true, Bool.true_eq_false, false_and, true_and,
          List.nil_eq, and_true] at hxy hyz <;>
        simp only [sameDeclaringScope, Bool.and_eq_true, beq_iff_eq, and_true,
          Bool.false_eq_true, and_false] at h1 h2 ⊢
      all_goals first
        | exact h1.trans h2
        | exact ⟨h1.1.trans h2.1, h1.2.trans h2.2⟩
        | exact ⟨⟨h1.1.1.trans h2.1.1, h1.1.2.trans h2.1.2⟩,
            same_declaring_scope_trans p q r hxy hyz h1.2 h2.2⟩

/-! ### `compatibleActivations` in both directions is equality of activation chains -/

/-- The activation of each level of a chain, innermost first. -/
def activationChain : Option ScopeCtx → List (Option Nat)
  | none => []
  | some (.mk p _ _ _ _ _ activation _) => activation :: activationChain p

theorem compatible_activations_both_iff : ∀ r a : Option ScopeCtx,
    (compatibleActivations r a = true ∧ compatibleActivations a r = true) ↔
      activationChain r = activationChain a
  | none, none => by simp [compatibleActivations, activationChain]
  | none, some (.mk _ _ _ _ _ _ _ _) => by simp [compatibleActivations, activationChain]
  | some (.mk _ _ _ _ _ _ _ _), none => by simp [compatibleActivations, activationChain]
  | some (.mk rp _ _ _ _ _ ra _), some (.mk ap _ _ _ _ _ aa _) => by
      have ih := compatible_activations_both_iff rp ap
      simp only [compatibleActivations, activationChain, Bool.and_eq_true, List.cons.injEq]
      constructor
      · rintro ⟨⟨h1, h2⟩, h3, h4⟩
        refine ⟨?_, ih.mp ⟨h2, h4⟩⟩
        cases ra <;> cases aa <;> simp_all
      · rintro ⟨rfl, h⟩
        have := ih.mpr h
        cases ra <;> simp_all

theorem compatible_activations_refl (s : Option ScopeCtx) : compatibleActivations s s = true :=
  ((compatible_activations_both_iff s s).mpr rfl).1

/-! ### Repeated callable identity: reflexive, symmetric, transitive on its domain -/

/-- Declaring-scope sameness of two optional parents (the parent comparison of
    `sameRepeatedCallableIdentity`). -/
def sameParent : Option ScopeCtx → Option ScopeCtx → Bool
  | none, none => true
  | some p, some q => sameDeclaringScope p q
  | _, _ => false

/-- The builtin an algorithm is, if it is one. -/
def asBuiltin? : Algorithm → Option Builtin
  | .builtin b => some b
  | _ => none

/-- The comparison of two non-builtin algorithms. -/
def identityCore (a b : Algorithm) : Bool :=
  a.declarationId == b.declarationId && sameParent a.parent b.parent &&
    compatibleActivations a.parent b.parent && compatibleActivations b.parent a.parent

/-- `sameRepeatedCallableIdentity` in two layers: builtins by their tag, two non-builtins by
    `identityCore`, a builtin and a non-builtin never. -/
theorem same_identity_eq (a b : Algorithm) :
    sameRepeatedCallableIdentity a b =
      match asBuiltin? a, asBuiltin? b with
      | some x, some y => x == y
      | none, none => identityCore a b
      | _, _ => false := by
  cases a <;> cases b <;> rfl

theorem same_parent_refl (p : Option ScopeCtx) : sameParent p p = true := by
  cases p <;> simp [sameParent, same_declaring_scope_refl]

theorem same_parent_symm (p q : Option ScopeCtx) : sameParent p q = sameParent q p := by
  cases p <;> cases q <;> simp [sameParent, same_declaring_scope_symm]

theorem same_parent_trans (p q r : Option ScopeCtx)
    (h1 : p.map idProfile = q.map idProfile) (h2 : q.map idProfile = r.map idProfile)
    (hpq : sameParent p q = true) (hqr : sameParent q r = true) : sameParent p r = true := by
  rcases p with _ | p <;> rcases q with _ | q <;> rcases r with _ | r <;>
    simp_all [sameParent]
  exact same_declaring_scope_trans p q r (h1.trans h2.symm) h2 hpq hqr

theorem identity_core_refl (a : Algorithm) : identityCore a a = true := by
  simp [identityCore, same_parent_refl, compatible_activations_refl]

theorem identity_core_symm (a b : Algorithm) : identityCore a b = identityCore b a := by
  simp only [identityCore]
  rw [beq_comm_of_lawful a.declarationId, same_parent_symm a.parent]
  cases compatibleActivations a.parent b.parent <;> cases compatibleActivations b.parent a.parent <;>
    simp

/-- The parent chain's id profile: the transitivity DOMAIN of callable identity. -/
def parentProfile (a : Algorithm) : Option (List Bool) := a.parent.map idProfile

theorem identity_core_trans (a b c : Algorithm)
    (h1 : parentProfile a = parentProfile b) (h2 : parentProfile b = parentProfile c)
    (hab : identityCore a b = true) (hbc : identityCore b c = true) : identityCore a c = true := by
  simp only [identityCore, Bool.and_eq_true, beq_iff_eq] at hab hbc ⊢
  obtain ⟨⟨⟨d1, s1⟩, c1⟩, c1'⟩ := hab
  obtain ⟨⟨⟨d2, s2⟩, c2⟩, c2'⟩ := hbc
  have e1 := (compatible_activations_both_iff a.parent b.parent).mp ⟨c1, c1'⟩
  have e2 := (compatible_activations_both_iff b.parent c.parent).mp ⟨c2, c2'⟩
  have e := (compatible_activations_both_iff a.parent c.parent).mpr (e1.trans e2)
  exact ⟨⟨⟨d1.trans d2, same_parent_trans _ _ _ h1 h2 s1 s2⟩, e.1⟩, e.2⟩

/-- REFLEXIVITY of repeated callable identity, for every algorithm. -/
theorem same_identity_refl (a : Algorithm) : sameRepeatedCallableIdentity a a = true := by
  rw [same_identity_eq]
  cases h : asBuiltin? a <;> simp [identity_core_refl]

/-- SYMMETRY of repeated callable identity, for every pair of algorithms. -/
theorem same_identity_symm (a b : Algorithm) :
    sameRepeatedCallableIdentity a b = sameRepeatedCallableIdentity b a := by
  rw [same_identity_eq, same_identity_eq]
  cases asBuiltin? a <;> cases asBuiltin? b <;> simp [identity_core_symm, beq_comm_of_lawful]

/-- TRANSITIVITY of repeated callable identity on its DOMAIN: three algorithms whose parent
    chains have the same id profile (`parentProfile`; builtins and parentless algorithms
    have profile `none`). -/
theorem same_identity_trans (a b c : Algorithm)
    (h1 : parentProfile a = parentProfile b) (h2 : parentProfile b = parentProfile c)
    (hab : sameRepeatedCallableIdentity a b = true) (hbc : sameRepeatedCallableIdentity b c = true) :
    sameRepeatedCallableIdentity a c = true := by
  rw [same_identity_eq] at hab hbc ⊢
  cases ha : asBuiltin? a <;> cases hb : asBuiltin? b <;> cases hc : asBuiltin? c <;>
    simp_all [beq_iff_eq]
  exact identity_core_trans a b c (h1.trans h2.symm) h2 hab hbc

/-! ## The representative fold over stable completed contributions -/

/-- One STABLE COMPLETED contribution to a repeated name: the address the binder would bind,
    its complete counted VALUE and its CALLABLE identity, if any. -/
structure Contribution where
  address : Nat
  value : CountedResult
  callable : Option Algorithm

/-- Which comparison of NEED-04 refused a contribution: the counted VALUE (the binder's
    `badArity` under the repeated-parameter context) or the CALLABLE identity (its
    `typeMismatch`); in family mode either is a non-match. -/
inductive Conflict where
  | value
  | callable
  deriving DecidableEq, Repr

/-- ONE OCCURRENCE against the retained representative, exactly as `NeedBinder.bindName`
    decides it: the counted values first (`before == value`, representative first), then the
    two callable identities when both are present; the representative is KEPT unless it has no
    callable identity and the occurrence has one. -/
def retainStep (rep c : Contribution) : Except Conflict Contribution :=
  if !(rep.value == c.value) then .error .value
  else
    let keep : Except Conflict Contribution :=
      if (rep.callable.isSome || c.callable.isNone) = true then .ok rep else .ok c
    match rep.callable, c.callable with
    | some a, some b => if !sameRepeatedCallableIdentity a b then .error .callable else keep
    | _, _ => keep

/-- The representative a repeated name retains after its later contributions `cs`, starting
    from its first contribution `rep`; the first refused contribution ends the fold. -/
def retain (rep : Contribution) : List Contribution → Except Conflict Contribution
  | [] => .ok rep
  | c :: cs =>
    match retainStep rep c with
    | .error e => .error e
    | .ok next => retain next cs

/-- A callable identity some contribution of `l` carries. -/
def Present (l : List Contribution) (a : Algorithm) : Prop := ∃ x ∈ l, x.callable = some a

/-- PAIRWISE COMPATIBILITY: every two contributions have equal counted values and every two
    PRESENT callable identities are the same identity. -/
def Compatible (l : List Contribution) : Prop :=
  (∀ x ∈ l, ∀ y ∈ l, x.value = y.value) ∧
  (∀ x ∈ l, ∀ y ∈ l, ∀ a b, x.callable = some a → y.callable = some b →
    sameRepeatedCallableIdentity a b = true)

/-- TRANSITIVITY of callable identity among the identities present in `l` (the premise the
    laws need; `callable_trans_on_of_profiles` discharges it on the identity domain). -/
def CallableTransOn (l : List Contribution) : Prop :=
  ∀ a b c, Present l a → Present l b → Present l c →
    sameRepeatedCallableIdentity a b = true → sameRepeatedCallableIdentity b c = true →
    sameRepeatedCallableIdentity a c = true

/-- The premise is met whenever every present callable identity lies in the identity domain
    with one common parent profile (for instance: all builtins, or all declared under the same
    shape of scope chain). -/
theorem callable_trans_on_of_profiles (l : List Contribution) (profile : Option (List Bool))
    (h : ∀ a, Present l a → parentProfile a = profile) : CallableTransOn l := by
  intro a b c ha hb hc hab hbc
  exact same_identity_trans a b c ((h a ha).trans (h b hb).symm) ((h b hb).trans (h c hc).symm) hab hbc

theorem retainStep_cases (rep c : Contribution) (r : Contribution) (h : retainStep rep c = .ok r) :
    rep.value = c.value ∧
    (∀ a b, rep.callable = some a → c.callable = some b → sameRepeatedCallableIdentity a b = true) ∧
    ((rep.callable.isSome = true ∧ r = rep) ∨ (rep.callable = none ∧ c.callable = none ∧ r = rep) ∨
      (rep.callable = none ∧ c.callable.isSome = true ∧ r = c)) := by
  unfold retainStep at h
  by_cases hv : (rep.value == c.value) = true
  · have hv' : rep.value = c.value := by simpa using hv
    simp only [hv, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
    refine ⟨hv', ?_, ?_⟩
    · intro a b ha hb
      rw [ha, hb] at h
      by_cases hs : sameRepeatedCallableIdentity a b = true
      · exact hs
      · simp [hs] at h
    · rcases hr : rep.callable with _ | a <;> rcases hc : c.callable with _ | b <;>
        simp_all
      · by_cases hs : sameRepeatedCallableIdentity a b = true <;> simp_all
  · simp [hv] at h

theorem retainStep_ok_of_compatible (rep c : Contribution) (hv : rep.value = c.value)
    (hc : ∀ a b, rep.callable = some a → c.callable = some b → sameRepeatedCallableIdentity a b = true) :
    ∃ r, retainStep rep c = .ok r ∧ (r = rep ∨ r = c) := by
  unfold retainStep
  simp only [hv, beq_self_eq_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  rcases hr : rep.callable with _ | a <;> rcases hcc : c.callable with _ | b <;> simp
  simp [hc a b hr hcc]

/-- RESULT 3: the retained contribution is one of the supplied ones. -/
theorem retain_mem : ∀ (rep : Contribution) (cs : List Contribution) (r : Contribution),
    retain rep cs = .ok r → r ∈ rep :: cs
  | rep, [], r, h => by simp [retain] at h; simp [h]
  | rep, c :: cs, r, h => by
      simp only [retain] at h
      split at h
      · simp at h
      · rename_i next hstep
        obtain ⟨-, -, hcase⟩ := retainStep_cases rep c next hstep
        have hm := retain_mem next cs r h
        rcases hcase with ⟨-, rfl⟩ | ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩
        · simp only [List.mem_cons] at hm ⊢
          rcases hm with hm | hm
          · exact Or.inl hm
          · exact Or.inr (Or.inr hm)
        · simp only [List.mem_cons] at hm ⊢
          rcases hm with hm | hm
          · exact Or.inl hm
          · exact Or.inr (Or.inr hm)
        · simp only [List.mem_cons] at hm ⊢
          exact Or.inr hm

/-- Success from a compatible supply: every step's two contributions are compatible. -/
theorem retain_ok_of_compatible (L : List Contribution) (hL : Compatible L) :
    ∀ (rep : Contribution) (cs : List Contribution), rep ∈ L → (∀ c ∈ cs, c ∈ L) →
      ∃ r, retain rep cs = .ok r
  | rep, [], _, _ => ⟨rep, rfl⟩
  | rep, c :: cs, hrep, hcs => by
      have hc : c ∈ L := hcs c List.mem_cons_self
      obtain ⟨r, hr, hrm⟩ := retainStep_ok_of_compatible rep c (hL.1 rep hrep c hc)
        (fun a b ha hb => hL.2 rep hrep c hc a b ha hb)
      have hrL : r ∈ L := by rcases hrm with rfl | rfl <;> assumption
      obtain ⟨r', h'⟩ := retain_ok_of_compatible L hL r cs hrL (fun x hx => hcs x (List.mem_cons_of_mem _ hx))
      exact ⟨r', by simp only [retain, hr]; exact h'⟩

/-- THE FOLD INVARIANT: after the contributions `seen`, the representative carries their common
    counted value, and its callable identity is present and the same as every callable identity
    seen — the RICHER representative is what lets a later conflict surface. -/
def Retained (seen : List Contribution) (rep : Contribution) : Prop :=
  (∀ x ∈ seen, x.value = rep.value) ∧
  (∀ x ∈ seen, ∀ a, x.callable = some a →
    ∃ r, rep.callable = some r ∧ sameRepeatedCallableIdentity r a = true) ∧
  (∀ r, rep.callable = some r → Present seen r)

theorem retained_step (seen : List Contribution) (rep c next : Contribution)
    (hinv : Retained seen rep) (hstep : retainStep rep c = .ok next) :
    Retained (seen ++ [c]) next := by
  obtain ⟨hv, hcal, hcase⟩ := retainStep_cases rep c next hstep
  obtain ⟨iv, ic, ip⟩ := hinv
  rcases hcase with ⟨hsome, rfl⟩ | ⟨hnone, hcnone, rfl⟩ | ⟨hnone, hcsome, rfl⟩
  · obtain ⟨ra, hra⟩ := Option.isSome_iff_exists.mp hsome
    refine ⟨?_, ?_, ?_⟩
    · intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · exact iv x hx
      · simp at hx; subst hx; exact hv.symm
    · intro x hx a ha
      rcases List.mem_append.mp hx with hx | hx
      · exact ic x hx a ha
      · simp at hx; subst hx; exact ⟨ra, hra, hcal ra a hra ha⟩
    · intro r hr
      obtain ⟨y, hy, hyr⟩ := ip r hr
      exact ⟨y, List.mem_append_left _ hy, hyr⟩
  · refine ⟨?_, ?_, ?_⟩
    · intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · exact iv x hx
      · simp at hx; subst hx; exact hv.symm
    · intro x hx a ha
      rcases List.mem_append.mp hx with hx | hx
      · obtain ⟨r, hr, -⟩ := ic x hx a ha; rw [hnone] at hr; cases hr
      · simp at hx; subst hx; rw [hcnone] at ha; cases ha
    · intro r hr; rw [hnone] at hr; cases hr
  · obtain ⟨cb, hcb⟩ := Option.isSome_iff_exists.mp hcsome
    refine ⟨?_, ?_, ?_⟩
    · intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · exact (iv x hx).trans hv
      · simp at hx; subst hx; rfl
    · intro x hx a ha
      rcases List.mem_append.mp hx with hx | hx
      · obtain ⟨r, hr, -⟩ := ic x hx a ha; rw [hnone] at hr; cases hr
      · simp at hx; subst hx; rw [hcb] at ha; cases ha; exact ⟨cb, hcb, same_identity_refl cb⟩
    · intro r hr
      exact ⟨_, List.mem_append_right _ List.mem_cons_self, hr⟩

theorem retained_fold :
    ∀ (seen : List Contribution) (rep : Contribution) (cs : List Contribution) (r : Contribution),
      Retained seen rep → retain rep cs = .ok r → Retained (seen ++ cs) r
  | seen, rep, [], r, hinv, h => by simp [retain] at h; subst h; simpa using hinv
  | seen, rep, c :: cs, r, hinv, h => by
      simp only [retain] at h
      split at h
      · simp at h
      · rename_i next hstep
        have hnext := retained_step seen rep c next hinv hstep
        have := retained_fold (seen ++ [c]) next cs r hnext h
        simpa using this

theorem retained_initial (c : Contribution) : Retained [c] c := by
  refine ⟨?_, ?_, ?_⟩
  · intro x hx; simp at hx; subst hx; rfl
  · intro x hx a ha; simp at hx; subst hx; exact ⟨a, ha, same_identity_refl a⟩
  · intro r hr; exact ⟨c, by simp, hr⟩

/-- RESULT 1: success ⇔ pairwise compatibility (the forward direction on the identity domain,
    `CallableTransOn`; the backward direction needs no premise). -/
theorem retain_ok_iff_compatible (c : Contribution) (cs : List Contribution)
    (hT : CallableTransOn (c :: cs)) :
    (∃ r, retain c cs = .ok r) ↔ Compatible (c :: cs) := by
  constructor
  · rintro ⟨r, hr⟩
    have hinv := retained_fold [c] c cs r (retained_initial c) hr
    simp only [List.singleton_append] at hinv
    obtain ⟨iv, ic, ip⟩ := hinv
    refine ⟨fun x hx y hy => (iv x hx).trans (iv y hy).symm, ?_⟩
    intro x hx y hy a b ha hb
    obtain ⟨ra, hra, hsa⟩ := ic x hx a ha
    obtain ⟨rb, hrb, hsb⟩ := ic y hy b hb
    rw [hra] at hrb; cases hrb
    have hpr : Present (c :: cs) ra := ip ra hra
    exact hT a ra b ⟨x, hx, ha⟩ hpr ⟨y, hy, hb⟩ (by rw [same_identity_symm]; exact hsa) hsb
  · intro h
    exact retain_ok_of_compatible (c :: cs) h c cs List.mem_cons_self (fun x hx => List.mem_cons_of_mem _ hx)

theorem compatible_perm {l l' : List Contribution} (hp : l.Perm l') (h : Compatible l) : Compatible l' :=
  ⟨fun x hx y hy => h.1 x (hp.mem_iff.mpr hx) y (hp.mem_iff.mpr hy),
   fun x hx y hy => h.2 x (hp.mem_iff.mpr hx) y (hp.mem_iff.mpr hy)⟩

theorem callable_trans_on_perm {l l' : List Contribution} (hp : l.Perm l') (h : CallableTransOn l) :
    CallableTransOn l' := by
  intro a b c ha hb hc
  have pres : ∀ x, Present l' x → Present l x := fun x ⟨y, hy, hyx⟩ => ⟨y, hp.mem_iff.mpr hy, hyx⟩
  exact h a b c (pres a ha) (pres b hb) (pres c hc)

/-- RESULT 2: SATISFIABILITY IS PERMUTATION INVARIANT, incompatible combinations included —
    a permutation of the same contributions succeeds exactly when the original does. -/
theorem retain_satisfiable_perm (c d : Contribution) (cs ds : List Contribution)
    (hp : (c :: cs).Perm (d :: ds)) (hT : CallableTransOn (c :: cs)) :
    (∃ r, retain c cs = .ok r) ↔ (∃ r, retain d ds = .ok r) := by
  rw [retain_ok_iff_compatible c cs hT, retain_ok_iff_compatible d ds (callable_trans_on_perm hp hT)]
  exact ⟨compatible_perm hp, compatible_perm hp.symm⟩

/-- RESULT 4: the retained contribution has a callable identity iff some contribution has. -/
theorem retain_callable_isSome_iff (rep : Contribution) (cs : List Contribution) (r : Contribution)
    (h : retain rep cs = .ok r) :
    r.callable.isSome = true ↔ ∃ x ∈ rep :: cs, x.callable.isSome = true := by
  have hinv := retained_fold [rep] rep cs r (retained_initial rep) h
  simp only [List.singleton_append] at hinv
  obtain ⟨-, ic, ip⟩ := hinv
  constructor
  · intro hs
    obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp hs
    obtain ⟨x, hx, hxa⟩ := ip a ha
    exact ⟨x, hx, by simp [hxa]⟩
  · rintro ⟨x, hx, hs⟩
    obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp hs
    obtain ⟨b, hb, -⟩ := ic x hx a ha
    simp [hb]

/-- RESULT 5: FIRST AMONG THE RICHEST — for a fixed written order the retained contribution is
    the first one carrying a callable identity if any does, otherwise the first contribution. -/
theorem retain_first_richest_from : ∀ (rep : Contribution) (cs : List Contribution) (r : Contribution),
    retain rep cs = .ok r →
      r = if rep.callable.isSome then rep else (cs.find? (fun x => x.callable.isSome)).getD rep
  | rep, [], r, h => by simp [retain] at h; subst h; split <;> rfl
  | rep, c :: cs, r, h => by
      simp only [retain] at h
      split at h
      · simp at h
      · rename_i next hstep
        have ih := retain_first_richest_from next cs r h
        obtain ⟨-, -, hcase⟩ := retainStep_cases rep c next hstep
        rcases hcase with ⟨hs, rfl⟩ | ⟨hn, hcn, rfl⟩ | ⟨hn, hcs, rfl⟩
        · simp only [hs, ↓reduceIte] at ih ⊢; exact ih
        · simp only [hn, Option.isSome_none, Bool.false_eq_true, ↓reduceIte] at ih ⊢
          rw [ih, List.find?_cons]; simp [hcn]
        · simp only [hcs, ↓reduceIte] at ih
          simp only [hn, Option.isSome_none, Bool.false_eq_true, ↓reduceIte, List.find?_cons, hcs]
          simpa using ih

theorem retain_first_richest (c : Contribution) (cs : List Contribution) (r : Contribution)
    (h : retain c cs = .ok r) :
    r = ((c :: cs).find? (fun x => x.callable.isSome)).getD c := by
  rw [retain_first_richest_from c cs r h, List.find?_cons]
  cases hc : c.callable.isSome <;> simp

/-- RESULT 6: PERMUTATION PRESERVES THE OBSERVATION of a successful binding — the counted VALUE
    (value and emitted count), callable availability and callable identity; NOT the retained
    address or representation. -/
theorem retain_perm_preserves_observation (c d : Contribution) (cs ds : List Contribution)
    (hp : (c :: cs).Perm (d :: ds)) (hT : CallableTransOn (c :: cs)) (r r' : Contribution)
    (hr : retain c cs = .ok r) (hr' : retain d ds = .ok r') :
    r.value = r'.value ∧ r.callable.isSome = r'.callable.isSome ∧
      (∀ a b, r.callable = some a → r'.callable = some b → sameRepeatedCallableIdentity a b = true) := by
  have hcomp := (retain_ok_iff_compatible c cs hT).mp ⟨r, hr⟩
  have hm := retain_mem c cs r hr
  have hm' := hp.mem_iff.mpr (retain_mem d ds r' hr')
  refine ⟨hcomp.1 r hm r' hm', ?_, fun a b ha hb => hcomp.2 r hm r' hm' a b ha hb⟩
  have e1 := retain_callable_isSome_iff c cs r hr
  have e2 := retain_callable_isSome_iff d ds r' hr'
  have e3 : (∃ x ∈ c :: cs, x.callable.isSome = true) ↔ (∃ x ∈ d :: ds, x.callable.isSome = true) :=
    ⟨fun ⟨x, hx, h⟩ => ⟨x, hp.mem_iff.mp hx, h⟩, fun ⟨x, hx, h⟩ => ⟨x, hp.mem_iff.mpr hx, h⟩⟩
  rw [Bool.eq_iff_iff, e1, e2]
  exact e3

/-- THE OPTIONAL-CALLABLE TRAP: a value-only contribution between two conflicting callable
    identities cannot hide their conflict, because the richer representative is retained. -/
theorem retain_value_only_cannot_hide_a_conflict (x y z : Contribution) (a b : Algorithm)
    (hx : x.callable = some a) (hy : y.callable = none) (hz : z.callable = some b)
    (hxy : x.value = y.value) (hyz : y.value = z.value)
    (hab : sameRepeatedCallableIdentity a b = false) :
    retain x [y, z] = .error .callable := by
  simp [retain, retainStep, hx, hy, hz, hxy, hyz, hab]

/-! ## Result 7: the production traversal computes the fold -/

/-- STABLE OBSERVATIONS of a capability record on the cells `cells`, along an invariant `Inv` of
    the semantic state: every VALUE demand and CALLABLE projection of such a cell returns the
    cell's FIXED observation `obs` and re-establishes `Inv`. This is the "stable completed
    contribution" domain: it does NOT hold of a cell whose first demand fails, depends on the
    state, or is still suspended with a state-dependent outcome. -/
structure Stable (k : NeedCapabilities EvalM) (Inv : EvalState → Prop)
    (obs : Nat → CountedResult × Option Algorithm) (cells : List Nat) : Prop where
  value : ∀ a ∈ cells, ∀ s, Inv s → ∃ t, runEval (k.value a) s = (.ok (obs a).1, t) ∧ Inv t
  callable : ∀ a ∈ cells, ∀ s, Inv s → ∃ t, runEval (k.callable a) s = (.ok (obs a).2, t) ∧ Inv t

/-- The contribution a stable cell makes. -/
def contrib (obs : Nat → CountedResult × Option Algorithm) (a : Nat) : Contribution :=
  ⟨a, (obs a).1, (obs a).2⟩

/-- The binder's re-binding of one name (`bindName`'s final environment). -/
def rebind (bound : NeedEnv) (name : Ident) (address : Nat) : NeedEnv :=
  bound.filter (fun entry => entry.fst != name) ++ [(name, address)]

/-- LOCAL pure form of one `NeedBinder.bindName` occurrence over fixed observations; proved to be
    the production run by `name_step_production`. -/
def nameStep (obs : Nat → CountedResult × Option Algorithm) (repeated : List Ident) (family : Bool)
    (bound : NeedEnv) (name : Ident) (address : Nat) : Except Error (Option NeedEnv) :=
  if repeated.contains name then
    match lookupAssoc name bound with
    | none => .ok (some (rebind bound name address))
    | some previous =>
      if (!((obs previous).1 == (obs address).1)) = true then
        (if family then .ok none
          else .error (Error.withContext (repeatedParameterContext name) Error.badArity))
      else repeatedVerdict name address bound family (obs previous).2 (obs address).2
  else .ok (some (rebind bound name address))

theorem lookupAssoc_some_mem : ∀ (n : Ident) (bound : NeedEnv) (v : Nat),
    lookupAssoc n bound = some v → ∃ e ∈ bound, e.2 = v
  | _, [], _, h => by simp [lookupAssoc] at h
  | n, (k, w) :: rest, v, h => by
      simp only [lookupAssoc] at h
      split at h
      · cases h; exact ⟨(k, w), List.mem_cons_self, rfl⟩
      · obtain ⟨e, he, hv⟩ := lookupAssoc_some_mem n rest v h
        exact ⟨e, List.mem_cons_of_mem _ he, hv⟩

/-- ONE OCCURRENCE, production: on stable cells the generic core's `bindName` (hence the
    production `bindNeedName`) returns exactly `nameStep`. -/
theorem name_step_production (k : NeedCapabilities EvalM) (Inv : EvalState → Prop)
    (obs : Nat → CountedResult × Option Algorithm) (cells : List Nat) (hk : Stable k Inv obs cells)
    (name : Ident) (address : Nat) (repeated : List Ident) (bound : NeedEnv) (family : Bool)
    (s : EvalState) (ha : address ∈ cells) (hb : ∀ e ∈ bound, e.2 ∈ cells) (hs : Inv s) :
    ∃ t, Inv t ∧ runEval (NeedBinder.bindName k name address repeated bound family) s
      = (nameStep obs repeated family bound name address, t) := by
  by_cases hr : repeated.contains name = true
  · rw [repeated_name_binding k name address repeated bound family s hr]
    obtain ⟨t1, h1, i1⟩ := hk.value address ha s hs
    simp only [h1]
    cases hl : lookupAssoc name bound with
    | none => exact ⟨t1, i1, by simp only [nameStep, hr, hl, rebind, ↓reduceIte]⟩
    | some previous =>
      obtain ⟨e, he, hev⟩ := lookupAssoc_some_mem name bound previous hl
      have hp : previous ∈ cells := hev ▸ hb e he
      obtain ⟨t2, h2, i2⟩ := hk.value previous hp t1 i1
      simp only [h2]
      by_cases hbv : (!((obs previous).1 == (obs address).1)) = true
      · exact ⟨t2, i2, by simp only [nameStep, hr, hl, hbv, ↓reduceIte]⟩
      · obtain ⟨t3, h3, i3⟩ := hk.callable previous hp t2 i2
        obtain ⟨t4, h4, i4⟩ := hk.callable address ha t3 i3
        refine ⟨t4, i4, ?_⟩
        simp only [nameStep, hr, hl, hbv, h3, h4, ↓reduceIte, Bool.false_eq_true]
  · have hr' : repeated.contains name = false := by simpa using hr
    rw [BinderCore.core_plain_name_is_pure k name address repeated bound family hr']
    exact ⟨s, hs, by simp only [runEval_pure, nameStep, hr', rebind, Bool.false_eq_true, ↓reduceIte]⟩

theorem rebind_cells (cells : List Nat) (bound : NeedEnv) (name : Ident) (address : Nat)
    (ha : address ∈ cells) (hb : ∀ e ∈ bound, e.2 ∈ cells) : ∀ e ∈ rebind bound name address, e.2 ∈ cells := by
  intro e he
  rcases List.mem_append.mp he with he | he
  · exact hb e (List.mem_filter.mp he).1
  · simp at he; subst he; exact ha

/-- THE PRODUCTION VERDICT OF A REPEATED OCCURRENCE IS `retainStep`: with the name already bound
    to `p`, the occurrence at `a` keeps the binding exactly when `retainStep` keeps the
    representative, re-binds to `a` exactly when `retainStep` switches to the richer
    contribution, and refuses exactly when `retainStep` does — a family non-match, or the
    ordinary error of the refusing comparison (counted value: `badArity` under the
    repeated-parameter context; callable identity: `typeMismatch`). -/
theorem nameStep_repeated_spec (obs : Nat → CountedResult × Option Algorithm)
    (repeated : List Ident) (family : Bool) (bound : NeedEnv) (n : Ident) (a p : Nat)
    (hr : repeated.contains n = true) (hl : lookupAssoc n bound = some p) :
    (retainStep (contrib obs p) (contrib obs a) = .ok (contrib obs p) ∧
        nameStep obs repeated family bound n a = .ok (some bound)) ∨
    (retainStep (contrib obs p) (contrib obs a) = .ok (contrib obs a) ∧
        nameStep obs repeated family bound n a = .ok (some (rebind bound n a))) ∨
    (retainStep (contrib obs p) (contrib obs a) = .error .value ∧
        nameStep obs repeated family bound n a = (if family then .ok none
          else .error (Error.withContext (repeatedParameterContext n) Error.badArity))) ∨
    (retainStep (contrib obs p) (contrib obs a) = .error .callable ∧
        nameStep obs repeated family bound n a = (if family then .ok none
          else .error (Error.typeMismatch "Repeated bind equality requires the same callable identity"))) := by
  have hrm : n ∈ repeated := by simpa using hr
  cases hv : ((obs p).1 == (obs a).1)
  · refine Or.inr (Or.inr (Or.inl ⟨?_, ?_⟩))
    · simp [retainStep, contrib, hv]
    · simp only [nameStep, hr, hl, hv, Bool.not_false, ↓reduceIte]
  · rcases hf : (obs p).2 with _ | x <;> rcases hg : (obs a).2 with _ | y
    · exact Or.inl ⟨by simp [retainStep, contrib, hv, hf, hg],
        by simp [nameStep, hrm, hl, hv, hf, hg, repeatedVerdict]⟩
    · exact Or.inr (Or.inl ⟨by simp [retainStep, contrib, hv, hf, hg],
        by simp [nameStep, hrm, hl, hv, hf, hg, repeatedVerdict, rebind]⟩)
    · exact Or.inl ⟨by simp [retainStep, contrib, hv, hf, hg],
        by simp [nameStep, hrm, hl, hv, hf, hg, repeatedVerdict]⟩
    · cases hs : sameRepeatedCallableIdentity x y
      · exact Or.inr (Or.inr (Or.inr ⟨by simp [retainStep, contrib, hv, hf, hg, hs],
          by simp [nameStep, hrm, hl, hv, hf, hg, hs, repeatedVerdict]⟩))
      · exact Or.inl ⟨by simp [retainStep, contrib, hv, hf, hg, hs],
          by simp [nameStep, hrm, hl, hv, hf, hg, hs, repeatedVerdict]⟩

/-- (S3) The first occurrence of a repeated name, and every non-repeated name, re-binds. -/
theorem nameStep_rebinds (obs : Nat → CountedResult × Option Algorithm)
    (repeated : List Ident) (family : Bool) (bound : NeedEnv) (n : Ident) (a : Nat)
    (h : repeated.contains n = false ∨ lookupAssoc n bound = none) :
    nameStep obs repeated family bound n a = .ok (some (rebind bound n a)) := by
  rcases h with h | h
  · simp only [nameStep, h, Bool.false_eq_true, ↓reduceIte]
  · unfold nameStep; split <;> simp only [h]

/-- A successful occurrence keeps the environment or re-binds the name to the occurrence. -/
theorem nameStep_ok_cases (obs : Nat → CountedResult × Option Algorithm)
    (repeated : List Ident) (family : Bool) (bound next : NeedEnv) (n : Ident) (a : Nat)
    (h : nameStep obs repeated family bound n a = .ok (some next)) :
    next = bound ∨ next = rebind bound n a := by
  by_cases hr : repeated.contains n = true
  · cases hl : lookupAssoc n bound with
    | none => rw [nameStep_rebinds obs repeated family bound n a (Or.inr hl)] at h; cases h; exact Or.inr rfl
    | some p =>
      rcases nameStep_repeated_spec obs repeated family bound n a p hr hl with
        ⟨-, he⟩ | ⟨-, he⟩ | ⟨-, he⟩ | ⟨-, he⟩ <;> rw [he] at h
      · cases h; exact Or.inl rfl
      · cases h; exact Or.inr rfl
      · cases family <;> simp at h
      · cases family <;> simp at h
  · rw [nameStep_rebinds obs repeated family bound n a (Or.inl (by simpa using hr))] at h
    cases h; exact Or.inr rfl

theorem nameStep_cells (obs : Nat → CountedResult × Option Algorithm) (cells : List Nat)
    (repeated : List Ident) (family : Bool) (bound : NeedEnv) (name : Ident) (address : Nat)
    (next : NeedEnv) (ha : address ∈ cells) (hb : ∀ e ∈ bound, e.2 ∈ cells)
    (h : nameStep obs repeated family bound name address = .ok (some next)) : ∀ e ∈ next, e.2 ∈ cells := by
  rcases nameStep_ok_cases obs repeated family bound next name address h with rfl | rfl
  · exact hb
  · exact rebind_cells cells bound name address ha hb

/-- LOCAL pure form of a flat level of name patterns over fixed observations: the occurrences
    in written order, the first non-match or failure ending the level. -/
def flatBind (obs : Nat → CountedResult × Option Algorithm) (repeated : List Ident) (family : Bool) :
    NeedEnv → List (Ident × Nat) → Except Error (Option NeedEnv)
  | bound, [] => .ok (some bound)
  | bound, (n, a) :: rest =>
    match nameStep obs repeated family bound n a with
    | .ok (some next) => flatBind obs repeated family next rest
    | other => other

/-- The name patterns of a flat level. -/
def namePatterns (pairs : List (Ident × Nat)) : List NeedPattern := pairs.map (fun p => NeedPattern.bind p.1)

/-- Its supplied cells, one per pattern. -/
def cellSources (pairs : List (Ident × Nat)) : List (NeedSource Nat) := pairs.map (fun p => NeedSource.cell p.2)

/-- A FLAT LEVEL, production: the generic core's `bindSources` over a flat level of name
    patterns, each from its supplied stable cell, returns exactly `flatBind`. -/
theorem flat_level_is_flatBind (k : NeedCapabilities EvalM) (Inv : EvalState → Prop)
    (obs : Nat → CountedResult × Option Algorithm) (cells : List Nat) (hk : Stable k Inv obs cells)
    (repeated : List Ident) (family : Bool) :
    ∀ (pairs : List (Ident × Nat)) (bound : NeedEnv) (s : EvalState),
      (∀ p ∈ pairs, p.2 ∈ cells) → (∀ e ∈ bound, e.2 ∈ cells) → Inv s →
      ∃ t, Inv t ∧ runEval (NeedBinder.bindSources k (namePatterns pairs) (cellSources pairs) repeated bound family) s
        = (flatBind obs repeated family bound pairs, t)
  | [], bound, s, _, _, hs => ⟨s, hs, rfl⟩
  | (n, a) :: rest, bound, s, hp, hb, hs => by
      have ha : a ∈ cells := hp (n, a) List.mem_cons_self
      obtain ⟨t1, i1, h1⟩ := name_step_production k Inv obs cells hk n a repeated bound family s ha hb hs
      simp only [namePatterns, cellSources, List.map_cons, NeedBinder.bindSources, List.headD_cons,
        List.tail_cons, NeedBinder.sourceAddress, runEval_bind, runEval_pure, thenRun_ok, NeedBinder.bindOne]
      rw [h1]
      cases hns : nameStep obs repeated family bound n a with
      | error e => exact ⟨t1, i1, by simp [flatBind, hns]⟩
      | ok r =>
        cases r with
        | none => exact ⟨t1, i1, by simp [flatBind, hns]⟩
        | some next =>
          have hnext := nameStep_cells obs cells repeated family bound n a next ha hb hns
          obtain ⟨t, it, ht⟩ := flat_level_is_flatBind k Inv obs cells hk repeated family rest next t1
            (fun p hp' => hp p (List.mem_cons_of_mem _ hp')) hnext i1
          refine ⟨t, it, ?_⟩
          simp only [namePatterns, cellSources] at ht
          simp only [thenRun_ok]
          rw [ht]
          simp [flatBind, hns]

/-! ### Each name's binding is its own `retain` over its own occurrences -/

/-- The occurrences of `X` in a flat level, in written order. -/
def occ (X : Ident) (pairs : List (Ident × Nat)) : List Nat :=
  (pairs.filter (fun p => p.1 == X)).map Prod.snd

/-- The fold of one name from its state before the level (`start`, the cell it is bound to)
    over its occurrences. -/
def perName (obs : Nat → CountedResult × Option Algorithm) :
    Option Nat → List Nat → Option (Except Conflict Contribution)
  | none, [] => none
  | none, a :: as => some (retain (contrib obs a) (as.map (contrib obs)))
  | some p, as => some (retain (contrib obs p) (as.map (contrib obs)))

theorem occ_cons (X n : Ident) (a : Nat) (rest : List (Ident × Nat)) :
    occ X ((n, a) :: rest) = if n = X then a :: occ X rest else occ X rest := by
  by_cases h : n = X <;> simp [occ, h]

theorem retainStep_contrib (obs : Nat → CountedResult × Option Algorithm) (p a : Nat) (r : Contribution)
    (h : retainStep (contrib obs p) (contrib obs a) = .ok r) : r = contrib obs r.address := by
  obtain ⟨-, -, hcase⟩ := retainStep_cases _ _ r h
  rcases hcase with ⟨-, rfl⟩ | ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩ <;> rfl

/-- (S1) A successful repeated occurrence binds the name to the cell `retainStep` keeps and
    leaves every other name unchanged. -/
theorem nameStep_repeated_ok (obs : Nat → CountedResult × Option Algorithm)
    (repeated : List Ident) (family : Bool) (bound next : NeedEnv) (n : Ident) (a p : Nat)
    (hr : repeated.contains n = true) (hl : lookupAssoc n bound = some p)
    (h : nameStep obs repeated family bound n a = .ok (some next)) :
    ∃ r, retainStep (contrib obs p) (contrib obs a) = .ok r ∧ lookupAssoc n next = some r.address ∧
      ∀ X, X ≠ n → lookupAssoc X next = lookupAssoc X bound := by
  rcases nameStep_repeated_spec obs repeated family bound n a p hr hl with
    ⟨hs, he⟩ | ⟨hs, he⟩ | ⟨-, he⟩ | ⟨-, he⟩ <;> rw [he] at h
  · cases h
    exact ⟨_, hs, by simpa [contrib] using hl, fun _ _ => rfl⟩
  · cases h
    refine ⟨_, hs, by simp [rebind, BinderCorrespondence.lookupAssoc_rebind, contrib], ?_⟩
    intro X hX
    simp [rebind, BinderCorrespondence.lookupAssoc_rebind, hX]
  · cases family <;> simp at h
  · cases family <;> simp at h

/-- (S2) A repeated occurrence whose `retainStep` succeeds binds. -/
theorem nameStep_repeated_of_ok (obs : Nat → CountedResult × Option Algorithm)
    (repeated : List Ident) (family : Bool) (bound : NeedEnv) (n : Ident) (a p : Nat) (r : Contribution)
    (hr : repeated.contains n = true) (hl : lookupAssoc n bound = some p)
    (h : retainStep (contrib obs p) (contrib obs a) = .ok r) :
    ∃ next, nameStep obs repeated family bound n a = .ok (some next) := by
  rcases nameStep_repeated_spec obs repeated family bound n a p hr hl with
    ⟨-, he⟩ | ⟨-, he⟩ | ⟨hs, -⟩ | ⟨hs, -⟩
  · exact ⟨_, he⟩
  · exact ⟨_, he⟩
  · rw [hs] at h; cases h
  · rw [hs] at h; cases h

/-- SOUNDNESS OF THE PROJECTION: when the flat level binds, every repeated name is bound to the
    representative its own fold retains over its own occurrences, from its state before the
    level. -/
theorem flatBind_per_name (obs : Nat → CountedResult × Option Algorithm) (repeated : List Ident)
    (family : Bool) :
    ∀ (pairs : List (Ident × Nat)) (bound env : NeedEnv),
      flatBind obs repeated family bound pairs = .ok (some env) → ∀ X, repeated.contains X = true →
        match perName obs (lookupAssoc X bound) (occ X pairs) with
        | none => lookupAssoc X env = none
        | some (.ok r) => lookupAssoc X env = some r.address
        | some (.error _) => False
  | [], bound, env, h, X, _ => by
      simp [flatBind] at h; subst h
      cases hl : lookupAssoc X bound <;> simp [perName, occ, retain, contrib]
  | (n, a) :: rest, bound, env, h, X, hX => by
      simp only [flatBind] at h
      cases hns : nameStep obs repeated family bound n a with
      | error e => rw [hns] at h; cases h
      | ok o =>
        cases o with
        | none => rw [hns] at h; cases h
        | some next =>
          rw [hns] at h
          have ih := flatBind_per_name obs repeated family rest next env h X hX
          rw [occ_cons]
          by_cases hnX : n = X
          · subst hnX
            simp only [↓reduceIte]
            cases hl : lookupAssoc n bound with
            | none =>
              rw [nameStep_rebinds obs repeated family bound n a (Or.inr hl)] at hns
              cases hns
              simp only [rebind, BinderCorrespondence.lookupAssoc_rebind, ↓reduceIte] at ih
              simpa [perName] using ih
            | some p =>
              obtain ⟨r, hst, hln, -⟩ := nameStep_repeated_ok obs repeated family bound next n a p hX hl hns
              rw [hln] at ih
              have hr := retainStep_contrib obs p a r hst
              simp only [perName, List.map_cons, retain, hst]
              rw [hr]
              simpa [perName] using ih
          · simp only [hnX, ↓reduceIte]
            have hsame : lookupAssoc X next = lookupAssoc X bound := by
              by_cases hrn : repeated.contains n = true
              · cases hl : lookupAssoc n bound with
                | none =>
                  rw [nameStep_rebinds obs repeated family bound n a (Or.inr hl)] at hns
                  cases hns; simp [rebind, BinderCorrespondence.lookupAssoc_rebind, Ne.symm hnX]
                | some p =>
                  obtain ⟨_, _, _, hother⟩ := nameStep_repeated_ok obs repeated family bound next n a p hrn hl hns
                  exact hother X (Ne.symm hnX)
              · rw [nameStep_rebinds obs repeated family bound n a (Or.inl (by simpa using hrn))] at hns
                cases hns; simp [rebind, BinderCorrespondence.lookupAssoc_rebind, Ne.symm hnX]
            rw [hsame] at ih
            exact ih

/-- COMPLETENESS OF THE PROJECTION: when every repeated name's own fold succeeds, the flat
    level binds. -/
theorem flatBind_complete (obs : Nat → CountedResult × Option Algorithm) (repeated : List Ident)
    (family : Bool) :
    ∀ (pairs : List (Ident × Nat)) (bound : NeedEnv),
      (∀ X, repeated.contains X = true → ∀ e, perName obs (lookupAssoc X bound) (occ X pairs) ≠ some (.error e)) →
      ∃ env, flatBind obs repeated family bound pairs = .ok (some env)
  | [], bound, _ => ⟨bound, rfl⟩
  | (n, a) :: rest, bound, h => by
      have step : ∃ next, nameStep obs repeated family bound n a = .ok (some next) ∧
          ∀ X, repeated.contains X = true → ∀ e,
            perName obs (lookupAssoc X next) (occ X rest) ≠ some (.error e) := by
        by_cases hrn : repeated.contains n = true
        · cases hl : lookupAssoc n bound with
          | none =>
            refine ⟨rebind bound n a, nameStep_rebinds obs repeated family bound n a (Or.inr hl), ?_⟩
            intro X hX e
            have hX' := h X hX e
            rw [occ_cons] at hX'
            by_cases hnX : n = X
            · subst hnX
              simp only [↓reduceIte, hl, perName] at hX'
              simpa [rebind, BinderCorrespondence.lookupAssoc_rebind, perName] using hX'
            · simp only [hnX, ↓reduceIte] at hX'
              simpa [rebind, BinderCorrespondence.lookupAssoc_rebind, Ne.symm hnX] using hX'
          | some p =>
            have hn := h n hrn
            rw [occ_cons] at hn
            simp only [↓reduceIte, hl, perName, List.map_cons, retain] at hn
            cases hst : retainStep (contrib obs p) (contrib obs a) with
            | error e => exact absurd (by rw [hst]) (hn e)
            | ok r =>
              obtain ⟨next, hnext⟩ := nameStep_repeated_of_ok obs repeated family bound n a p r hrn hl hst
              obtain ⟨r', hst', hln, hother⟩ := nameStep_repeated_ok obs repeated family bound next n a p hrn hl hnext
              rw [hst] at hst'; cases hst'
              refine ⟨next, hnext, ?_⟩
              intro X hX e
              by_cases hnX : n = X
              · subst hnX
                have hr := retainStep_contrib obs p a r hst
                rw [hln]
                simp only [perName]
                intro hc
                apply hn e
                rw [hst]
                simp only
                rw [hr]
                simpa using hc
              · rw [hother X (Ne.symm hnX)]
                have hX' := h X hX e
                rw [occ_cons] at hX'
                simpa [hnX] using hX'
        · have hrn' : repeated.contains n = false := by simpa using hrn
          refine ⟨rebind bound n a, nameStep_rebinds obs repeated family bound n a (Or.inl hrn'), ?_⟩
          intro X hX e
          have hnX : n ≠ X := by intro he; subst he; rw [hrn'] at hX; cases hX
          have hX' := h X hX e
          rw [occ_cons] at hX'
          simp only [hnX, ↓reduceIte] at hX'
          simpa [rebind, BinderCorrespondence.lookupAssoc_rebind, Ne.symm hnX] using hX'
      obtain ⟨next, hns, hrest⟩ := step
      obtain ⟨env, henv⟩ := flatBind_complete obs repeated family rest next hrest
      exact ⟨env, by simp [flatBind, hns, henv]⟩

/-! ### The production head -/

theorem flat_head_accepts (names : List Ident) :
    needAcceptsCardinality (names.map (fun n => NeedPattern.bind n)) names.length = true := by
  have hf : (names.map (fun n => NeedPattern.bind n)).filter NeedPattern.isCollecting = [] := by
    induction names with
    | nil => rfl
    | cons n ns ih => simp [NeedPattern.isCollecting, ih]
  simp [needAcceptsCardinality, needMinimumSuppliedSlots, hf]

theorem flat_head_sources (names : List Ident) (cells : List Nat) (hlen : cells.length = names.length) :
    needLevelSources (names.map (fun n => NeedPattern.bind n)) cells = cells.map NeedSource.cell := by
  apply need_level_sources_without_collector
  · induction names with
    | nil => rfl
    | cons n ns ih => simp [List.findIdx?_cons, NeedPattern.isCollecting]
  · simpa using hlen

theorem flat_head_shape (names : List Ident) (cells : List Nat) (hlen : cells.length = names.length) :
    names.map (fun n => NeedPattern.bind n) = namePatterns (names.zip cells) ∧
      cells.map NeedSource.cell = cellSources (names.zip cells) := by
  induction names generalizing cells with
  | nil => cases cells with
    | nil => exact ⟨rfl, rfl⟩
    | cons _ _ => simp at hlen
  | cons n ns ih => cases cells with
    | nil => simp at hlen
    | cons c cs =>
      obtain ⟨h1, h2⟩ := ih cs (by simpa using hlen)
      exact ⟨by simp [namePatterns] at h1 ⊢; exact h1, by simp [cellSources] at h2 ⊢; exact h2⟩

/-- RESULT 7, PRODUCTION: the generic core's `bindPatterns` (by definition the production
    `bindNeedPatterns` at `NeedChannels.capabilities`, `bind_need_patterns_is_core`) over a flat
    head of name patterns and its stable supplied cells returns exactly `flatBind` over the
    written (name, cell) pairs. -/
theorem production_flat_head_is_flatBind (k : NeedCapabilities EvalM) (Inv : EvalState → Prop)
    (obs : Nat → CountedResult × Option Algorithm) (names : List Ident) (cells : List Nat)
    (hk : Stable k Inv obs cells) (hlen : cells.length = names.length) (family : Bool)
    (s : EvalState) (hs : Inv s) :
    ∃ t, Inv t ∧ runEval (NeedBinder.bindPatterns k (names.map (fun n => NeedPattern.bind n)) cells family) s
      = (flatBind obs (needRepeatedNames (names.map (fun n => NeedPattern.bind n))) family [] (names.zip cells), t) := by
  obtain ⟨hps, hsrc⟩ := flat_head_shape names cells hlen
  have hacc := flat_head_accepts names
  rw [← hlen] at hacc
  simp only [NeedBinder.bindPatterns, NeedBinder.bindLevel, NeedBinder.cardinalityGate, hacc,
    Bool.not_true, Bool.false_eq_true, ↓reduceIte, flat_head_sources names cells hlen, hsrc]
  conv => enter [1, t, 2, 1, 1, 2]; rw [hps]
  exact flat_level_is_flatBind k Inv obs cells hk _ family (names.zip cells) [] s
    (fun p hp => (List.of_mem_zip hp).2) (by simp) hs

/-- RESULT 7, CONSEQUENCE: when the production binding of a flat head succeeds, each repeated
    name is bound to the representative `retain` keeps over that name's own supplied
    contributions, in written order — so results 1–6 describe the production binding. -/
theorem production_flat_binding_is_retain (k : NeedCapabilities EvalM) (Inv : EvalState → Prop)
    (obs : Nat → CountedResult × Option Algorithm) (names : List Ident) (cells : List Nat)
    (hk : Stable k Inv obs cells) (hlen : cells.length = names.length) (family : Bool)
    (s t : EvalState) (hs : Inv s) (env : NeedEnv)
    (hrun : runEval (NeedBinder.bindPatterns k (names.map (fun n => NeedPattern.bind n)) cells family) s
      = (.ok (some env), t))
    (X : Ident) (hX : (needRepeatedNames (names.map (fun n => NeedPattern.bind n))).contains X = true)
    (a : Nat) (as : List Nat) (hocc : occ X (names.zip cells) = a :: as) :
    ∃ r, retain (contrib obs a) (as.map (contrib obs)) = .ok r ∧ lookupAssoc X env = some r.address := by
  obtain ⟨t', -, h⟩ := production_flat_head_is_flatBind k Inv obs names cells hk hlen family s hs
  rw [hrun] at h
  have hfb : flatBind obs (needRepeatedNames (names.map (fun n => NeedPattern.bind n))) family []
      (names.zip cells) = .ok (some env) := by
    have := congrArg Prod.fst h; simpa using this.symm
  have := flatBind_per_name obs (needRepeatedNames (names.map (fun n => NeedPattern.bind n))) family
    (names.zip cells) [] env hfb X hX
  simp only [lookupAssoc, hocc, perName] at this
  split at this
  · rename_i heq; cases heq
  · rename_i r heq; simp at heq; exact ⟨r, heq, this⟩
  · exact this.elim

/-- RESULT 7, SATISFIABILITY: the production binding of a flat head with stable cells succeeds
    exactly when every repeated name's own fold succeeds. -/
theorem production_flat_binding_succeeds_iff (k : NeedCapabilities EvalM) (Inv : EvalState → Prop)
    (obs : Nat → CountedResult × Option Algorithm) (names : List Ident) (cells : List Nat)
    (hk : Stable k Inv obs cells) (hlen : cells.length = names.length) (family : Bool)
    (s : EvalState) (hs : Inv s) :
    (∃ env t, runEval (NeedBinder.bindPatterns k (names.map (fun n => NeedPattern.bind n)) cells family) s
      = (.ok (some env), t)) ↔
    ∀ X, (needRepeatedNames (names.map (fun n => NeedPattern.bind n))).contains X = true →
      ∀ a as, occ X (names.zip cells) = a :: as → ∃ r, retain (contrib obs a) (as.map (contrib obs)) = .ok r := by
  obtain ⟨t', -, h⟩ := production_flat_head_is_flatBind k Inv obs names cells hk hlen family s hs
  constructor
  · rintro ⟨env, t, hrun⟩ X hX a as hocc
    obtain ⟨r, hr, -⟩ := production_flat_binding_is_retain k Inv obs names cells hk hlen family s t hs env hrun X hX a as hocc
    exact ⟨r, hr⟩
  · intro hall
    obtain ⟨env, henv⟩ := flatBind_complete obs (needRepeatedNames (names.map (fun n => NeedPattern.bind n)))
      family (names.zip cells) [] (by
      intro X hX e hc
      simp only [lookupAssoc] at hc
      cases hocc : occ X (names.zip cells) with
      | nil => rw [hocc] at hc; simp [perName] at hc
      | cons a as =>
        rw [hocc] at hc
        obtain ⟨r, hr⟩ := hall X hX a as hocc
        simp [perName, hr] at hc)
    exact ⟨env, t', by rw [h, henv]⟩

/-! ### A production instance of the VALUE half of stability -/

/-- Cells whose VALUE is already COMPLETED with the fixed observation. -/
def CompletedWith (obs : Nat → CountedResult × Option Algorithm) (cells : List Nat) (s : EvalState) : Prop :=
  ∀ a ∈ cells, ∃ cell, s.needs[a]? = some cell ∧ cell.state = .completed (.ok (obs a).1)

/-- The total public VALUE channel `demandNeed` is stable on completed cells: it returns the
    memoized counted value and leaves the state unchanged (`NeedControl.completed_reuse`). S5
    left the CALLABLE half for the `partial` `projectNeedCallable` a premise; since S6a the
    evaluator's binder call sites pass the total shells (`NeedChannels.shell`), whose two
    channels are stable on completed and Ready cells as kernel theorems
    (`NestedRepeatedNames.shell_model_caps`). -/
theorem demand_need_stable_on_completed (obs : Nat → CountedResult × Option Algorithm) (cells : List Nat)
    (a : Nat) (ha : a ∈ cells) (s : EvalState) (hs : CompletedWith obs cells s) :
    ∃ t, runEval (demandNeed a) s = (.ok (obs a).1, t) ∧ CompletedWith obs cells t := by
  obtain ⟨cell, hc, hst⟩ := hs a ha
  exact ⟨s, KatLang.NeedControl.Production.completed_reuse a s cell (.ok (obs a).1) hc hst, hs⟩

end KatLang.RepeatedNameLaws
