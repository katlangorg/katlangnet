import KatLangArityLaws.RepeatedNameLaws

open KatLang KatLang.RepeatedNameLaws

/-!
# Repeated callable identity across mixed declaration profiles (R4 / Q-66, S6a, October 2026)

S5 proved `sameRepeatedCallableIdentity` reflexive and symmetric for every algorithm and
transitive when the three parent chains have the same declaration-id presence profile
(`same_identity_trans`, premise `parentProfile a = parentProfile b = parentProfile c`). This
module proves a restricted domain for the MIXED identified/anonymous case; unrestricted
transitivity remains open.

THE ONE NON-STRUCTURAL STEP. `sameDeclaringScope l r` compares two levels structurally when both
carry a declaration identity and otherwise falls back to `reprStr l.declaration ==
reprStr r.declaration`. `ScopeCtx.declaration` is `partial` and the derived `Repr` is opaque to
the kernel, so nothing is known about those strings except that string equality is an
equivalence. The fallback is reached between two levels of DIFFERENT presence (one identified,
one anonymous) exactly when the comparison walks down to such a pair — a CROSS fallback.

RESULTS.

1. `same_declaring_scope_trans_of_no_cross`: transitivity whenever neither compared pair takes a
   cross fallback that SUCCEEDS (`NoCrossFallback`), with NO profile premise. The domain is
   strictly broader than S5's equal-profile domain (`no_cross_of_profiles`; the kernel witness
   `broader_than_equal_profiles` has unequal profiles below an anonymous level).
2. `same_declaring_scope_profile_aligned`: a successful comparison without a cross fallback
   compares identified with identified and anonymous with anonymous at every level it reads.
3. `same_identity_trans_of_no_cross`, `callable_trans_on_of_no_cross`: the same at the algorithm
   level, discharging `CallableTransOn` for every contribution list whose present identities
   pairwise avoid a cross fallback.
4. `same_identity_trans_of_separating`, `callable_trans_on_of_separating`: FULL transitivity for
   every algorithm, every list — under ONE explicit residual, `ReprSeparatesPresence`: the
   printed declaration of an identified scope never equals that of an anonymous one. It is not a
   kernel fact (opaque `partial` printer) and is NOT assumed anywhere else; executable evidence
   only (`CallableIdentityDomainGuards`).
5. `intransitive_identity_breaks_permutation`: what would fail without it. Any intransitive
   triple — which needs a successful cross fallback (`intransitivity_needs_a_cross_fallback`) —
   makes repeated-name SATISFIABILITY order dependent (result 2 of `RepeatedNameLaws`): one order
   fails with a callable conflict, a permutation of the same contributions succeeds.

No identity semantics changed. The optional-callable trap is independent of all of this: under the
group-aware NEED-04 fold it follows from `gfold_ok_iff_compatible` (`RepeatedNameLaws`) and is guarded in
`RepeatedNameGuards` § The optional-callable trap (the former `retain` fold and its
`retain_value_only_cannot_hide_a_conflict` were superseded, ALIAS-UNIFY-1).
-/

namespace KatLang.CallableIdentityDomain

/-- Two compared levels NEVER decide a mixed-presence pair through printed declarations: the
    comparison of `sameDeclaringScope` either stays structural (both identified), compares two
    anonymous levels, or meets a mixed pair whose printed declarations differ. -/
def NoCrossFallback : ScopeCtx → ScopeCtx → Prop
  | .mk p _ _ _ _ _ _ (some _), .mk q _ _ _ _ _ _ (some _) =>
      match p, q with
      | some p, some q => NoCrossFallback p q
      | _, _ => True
  | .mk _ _ _ _ _ _ _ none, .mk _ _ _ _ _ _ _ none => True
  | l, r => reprStr l.declaration ≠ reprStr r.declaration

/-- The comparison levels have the same presence: identified against identified (recursively, as
    far as both parents exist), anonymous against anonymous. -/
def Aligned : ScopeCtx → ScopeCtx → Prop
  | .mk p _ _ _ _ _ _ (some _), .mk q _ _ _ _ _ _ (some _) =>
      match p, q with
      | some p, some q => Aligned p q
      | _, _ => True
  | .mk _ _ _ _ _ _ _ none, .mk _ _ _ _ _ _ _ none => True
  | _, _ => False

/-- RESULT 2: a successful comparison without a cross fallback is presence-aligned. -/
theorem same_declaring_scope_profile_aligned : ∀ x y : ScopeCtx,
    NoCrossFallback x y → sameDeclaringScope x y = true → Aligned x y
  | .mk xp _ _ _ _ _ _ (some _), .mk yp _ _ _ _ _ _ (some _), hn, hs => by
      rcases xp with _ | p <;> rcases yp with _ | q <;> simp only [Aligned]
      simp only [NoCrossFallback] at hn
      simp only [sameDeclaringScope, Bool.and_eq_true] at hs
      exact same_declaring_scope_profile_aligned p q hn hs.2
  | .mk _ _ _ _ _ _ _ none, .mk _ _ _ _ _ _ _ none, _, _ => by simp only [Aligned]
  | .mk _ _ _ _ _ _ _ (some _), .mk _ _ _ _ _ _ _ none, hn, hs => by
      simp only [NoCrossFallback] at hn
      simp only [sameDeclaringScope, beq_iff_eq] at hs
      exact absurd hs hn
  | .mk _ _ _ _ _ _ _ none, .mk _ _ _ _ _ _ _ (some _), hn, hs => by
      simp only [NoCrossFallback] at hn
      simp only [sameDeclaringScope, beq_iff_eq] at hs
      exact absurd hs hn

/-- Transitivity on presence-aligned pairs (no profile premise). -/
theorem same_declaring_scope_trans_aligned : ∀ x y z : ScopeCtx,
    Aligned x y → Aligned y z →
    sameDeclaringScope x y = true → sameDeclaringScope y z = true → sameDeclaringScope x z = true
  | .mk xp xps _ _ _ _ _ (some a), .mk yp yps _ _ _ _ _ (some b), .mk zp zps _ _ _ _ _ (some c),
      hxy, hyz, h1, h2 => by
      rcases xp with _ | p <;> rcases yp with _ | q <;> rcases zp with _ | r <;>
        simp only [sameDeclaringScope, Bool.and_eq_true, beq_iff_eq, Bool.false_eq_true,
          and_false, and_true] at h1 h2 ⊢
      all_goals first
        | exact ⟨h1.1.trans h2.1, h1.2.trans h2.2⟩
        | (simp only [Aligned] at hxy hyz
           exact ⟨⟨h1.1.1.trans h2.1.1, h1.1.2.trans h2.1.2⟩,
             same_declaring_scope_trans_aligned p q r hxy hyz h1.2 h2.2⟩)
  | .mk _ _ _ _ _ _ _ none, .mk _ _ _ _ _ _ _ none, .mk _ _ _ _ _ _ _ none, _, _, h1, h2 => by
      simp only [sameDeclaringScope, beq_iff_eq] at h1 h2 ⊢
      exact h1.trans h2
  | .mk _ _ _ _ _ _ _ (some _), .mk _ _ _ _ _ _ _ none, _, hxy, _, _, _ => by
      simp only [Aligned] at hxy
  | .mk _ _ _ _ _ _ _ none, .mk _ _ _ _ _ _ _ (some _), _, hxy, _, _, _ => by
      simp only [Aligned] at hxy
  | .mk _ _ _ _ _ _ _ (some _), .mk _ _ _ _ _ _ _ (some _), .mk _ _ _ _ _ _ _ none, _, hyz, _, _ => by
      simp only [Aligned] at hyz
  | .mk _ _ _ _ _ _ _ none, .mk _ _ _ _ _ _ _ none, .mk _ _ _ _ _ _ _ (some _), _, hyz, _, _ => by
      simp only [Aligned] at hyz

/-- RESULT 1: TRANSITIVITY of declaring-scope sameness whenever neither compared pair decides a
    mixed-presence level through printed declarations. No profile premise. -/
theorem same_declaring_scope_trans_of_no_cross (x y z : ScopeCtx)
    (hxy : NoCrossFallback x y) (hyz : NoCrossFallback y z)
    (h1 : sameDeclaringScope x y = true) (h2 : sameDeclaringScope y z = true) :
    sameDeclaringScope x z = true :=
  same_declaring_scope_trans_aligned x y z
    (same_declaring_scope_profile_aligned x y hxy h1) (same_declaring_scope_profile_aligned y z hyz h2) h1 h2

/-- The S5 domain is inside the new one: chains with the same id-presence profile never meet a
    mixed-presence level. -/
theorem no_cross_of_profiles : ∀ x y : ScopeCtx, idProfile x = idProfile y → NoCrossFallback x y
  | .mk xp _ _ _ _ _ _ xid, .mk yp _ _ _ _ _ _ yid, h => by
      rcases xid with _ | a <;> rcases yid with _ | b <;>
        rcases xp with _ | p <;> rcases yp with _ | q <;>
        simp only [idProfile, List.cons.injEq, Option.isSome_some, Option.isSome_none,
          Bool.false_eq_true, Bool.true_eq_false, false_and, true_and, List.nil_eq,
          and_true] at h <;>
        simp only [NoCrossFallback]
      exact no_cross_of_profiles p q h

/-- A scope level with the given parent and declaration identity (every other field empty). -/
def level (parent : Option ScopeCtx) (id : Option PropertyIdentity) : ScopeCtx :=
  .mk parent [] [] [] [] [] none id

/-- STRICTLY BROADER than S5's domain (kernel witness): two chains anonymous at the top whose
    parents differ in presence have different id profiles, yet their comparison never leaves the
    anonymous fallback, so `NoCrossFallback` holds. -/
theorem broader_than_equal_profiles :
    NoCrossFallback (level (some (level none (some (.syntax 1)))) none) (level (some (level none none)) none) ∧
    idProfile (level (some (level none (some (.syntax 1)))) none) ≠ idProfile (level (some (level none none)) none) := by
  refine ⟨by simp only [level, NoCrossFallback], ?_⟩
  simp [level, idProfile]

/-! ## The residual: printed declarations separate presence -/

/-- THE ONE RESIDUAL OF FULL TRANSITIVITY: the printed declaration of an identified scope never
    equals the printed declaration of an anonymous one. `ScopeCtx.declaration` is `partial` and
    the derived `Repr` opaque, so this is not a kernel fact; no theorem outside this section
    assumes it. Executable evidence: `CallableIdentityDomainGuards`. -/
def ReprSeparatesPresence : Prop :=
  ∀ u v : ScopeCtx, u.declarationId.isSome = true → v.declarationId = none →
    reprStr u.declaration ≠ reprStr v.declaration

theorem no_cross_of_separating (hsep : ReprSeparatesPresence) : ∀ x y : ScopeCtx, NoCrossFallback x y
  | .mk xp _ _ _ _ _ _ (some a), .mk yp _ _ _ _ _ _ (some b) => by
      rcases xp with _ | p <;> rcases yp with _ | q <;> simp only [NoCrossFallback]
      exact no_cross_of_separating hsep p q
  | .mk _ _ _ _ _ _ _ none, .mk _ _ _ _ _ _ _ none => by simp only [NoCrossFallback]
  | .mk xp xps xo xpr xout xb xa (some a), .mk yp yps yo ypr yout yb ya none => by
      simp only [NoCrossFallback]
      exact hsep _ _ rfl rfl
  | .mk xp xps xo xpr xout xb xa none, .mk yp yps yo ypr yout yb ya (some b) => by
      simp only [NoCrossFallback]
      exact fun h => hsep _ _ rfl rfl h.symm

/-! ## Algorithm level -/

/-- Two optional parents whose comparison avoids a successful cross fallback. -/
def ParentNoCross : Option ScopeCtx → Option ScopeCtx → Prop
  | some p, some q => NoCrossFallback p q
  | _, _ => True

/-- Two algorithms' parent comparison avoids a successful cross fallback. -/
def IdentityNoCross (a b : Algorithm) : Prop := ParentNoCross a.parent b.parent

theorem same_parent_trans_of_no_cross (p q r : Option ScopeCtx)
    (h1 : ParentNoCross p q) (h2 : ParentNoCross q r)
    (hpq : sameParent p q = true) (hqr : sameParent q r = true) : sameParent p r = true := by
  rcases p with _ | p <;> rcases q with _ | q <;> rcases r with _ | r <;>
    simp_all [sameParent, ParentNoCross]
  exact same_declaring_scope_trans_of_no_cross p q r h1 h2 hpq hqr

/-- RESULT 3: TRANSITIVITY of repeated callable identity whenever neither compared pair takes a
    successful cross fallback — no profile premise. -/
theorem same_identity_trans_of_no_cross (a b c : Algorithm)
    (h1 : IdentityNoCross a b) (h2 : IdentityNoCross b c)
    (hab : sameRepeatedCallableIdentity a b = true) (hbc : sameRepeatedCallableIdentity b c = true) :
    sameRepeatedCallableIdentity a c = true := by
  rw [same_identity_eq] at hab hbc ⊢
  cases ha : asBuiltin? a <;> cases hb : asBuiltin? b <;> cases hc : asBuiltin? c <;>
    simp_all [beq_iff_eq]
  simp only [identityCore, Bool.and_eq_true, beq_iff_eq] at hab hbc ⊢
  obtain ⟨⟨⟨d1, s1⟩, c1⟩, c1'⟩ := hab
  obtain ⟨⟨⟨d2, s2⟩, c2⟩, c2'⟩ := hbc
  have e1 := (compatible_activations_both_iff a.parent b.parent).mp ⟨c1, c1'⟩
  have e2 := (compatible_activations_both_iff b.parent c.parent).mp ⟨c2, c2'⟩
  have e := (compatible_activations_both_iff a.parent c.parent).mpr (e1.trans e2)
  exact ⟨⟨⟨d1.trans d2, same_parent_trans_of_no_cross _ _ _ h1 h2 s1 s2⟩, e.1⟩, e.2⟩

/-- `CallableTransOn` for every list whose present identities pairwise avoid a successful cross
    fallback. -/
theorem callable_trans_on_of_no_cross (l : List Contribution)
    (h : ∀ a b, Present l a → Present l b → IdentityNoCross a b) : CallableTransOn l := by
  intro a b c ha hb hc hab hbc
  exact same_identity_trans_of_no_cross a b c (h a b ha hb) (h b c hb hc) hab hbc

/-- The S5 premise implies the new one. -/
theorem identity_no_cross_of_profiles (a b : Algorithm) (h : parentProfile a = parentProfile b) :
    IdentityNoCross a b := by
  unfold IdentityNoCross
  unfold parentProfile at h
  cases hp : a.parent <;> cases hq : b.parent <;>
    simp only [hp, hq, Option.map_some, ParentNoCross] at h ⊢
  exact no_cross_of_profiles _ _ (Option.some.inj h)

/-- RESULT 4: FULL transitivity, for every algorithm, under the one printed-declaration residual. -/
theorem same_identity_trans_of_separating (hsep : ReprSeparatesPresence) (a b c : Algorithm)
    (hab : sameRepeatedCallableIdentity a b = true) (hbc : sameRepeatedCallableIdentity b c = true) :
    sameRepeatedCallableIdentity a c = true := by
  have hn : ∀ x y : Algorithm, IdentityNoCross x y := by
    intro x y; unfold IdentityNoCross
    cases x.parent <;> cases y.parent <;> simp only [ParentNoCross]
    exact no_cross_of_separating hsep _ _
  exact same_identity_trans_of_no_cross a b c (hn a b) (hn b c) hab hbc

theorem callable_trans_on_of_separating (hsep : ReprSeparatesPresence) (l : List Contribution) :
    CallableTransOn l :=
  fun a b c _ _ _ hab hbc => same_identity_trans_of_separating hsep a b c hab hbc

/-! ## What fails without the residual -/

/-- An intransitive triple of callable identities needs a successful cross fallback in one of
    its two compared pairs. -/
theorem intransitivity_needs_a_cross_fallback (a b c : Algorithm)
    (hab : sameRepeatedCallableIdentity a b = true) (hbc : sameRepeatedCallableIdentity b c = true)
    (hac : sameRepeatedCallableIdentity a c = false) :
    ¬ IdentityNoCross a b ∨ ¬ IdentityNoCross b c := by
  by_cases h1 : IdentityNoCross a b
  · by_cases h2 : IdentityNoCross b c
    · have := same_identity_trans_of_no_cross a b c h1 h2 hab hbc
      rw [hac] at this; cases this
    · exact Or.inr h2
  · exact Or.inl h1

/-- RESULT 5: an intransitive triple would make repeated-name SATISFIABILITY ORDER DEPENDENT —
    three callable-bearing contributions with the identities `a`, `b`, `c`: NEED-04 compares every
    later identity with the group's FIRST one, so written `a, b, c` it refuses `c` (a callable
    conflict) and written `b, a, c` it accepts all three. So result 2 of `RepeatedNameLaws`
    (`gfold_satisfiable_perm`) needs `CallableTransOn`, and on such a triple it is false. -/
theorem intransitive_identity_breaks_permutation (v : CountedResult) (x y z : Nat) (a b c : Algorithm)
    (hab : sameRepeatedCallableIdentity a b = true) (hbc : sameRepeatedCallableIdentity b c = true)
    (hac : sameRepeatedCallableIdentity a c = false) :
    gfold {} [⟨x, v, some a⟩, ⟨y, v, some b⟩, ⟨z, v, some c⟩] = .error .callable ∧
    gfold {} [⟨y, v, some b⟩, ⟨x, v, some a⟩, ⟨z, v, some c⟩] =
      .ok { rep := some ⟨y, v, some b⟩, identity := some b, anchor := none,
            pending := [⟨y, v, some b⟩, ⟨x, v, some a⟩, ⟨z, v, some c⟩] } := by
  have hba : sameRepeatedCallableIdentity b a = true := by rw [same_identity_symm]; exact hab
  constructor
  · simp [gfold, gstep, GState.conflictsWith, GState.withCallable, hab, hac]
  · simp [gfold, gstep, GState.conflictsWith, GState.withCallable, hba, hbc]

end KatLang.CallableIdentityDomain
