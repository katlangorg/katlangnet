import KatLangArityLaws.SignatureCompletionEvaluation

open KatLang

/-!
# SC-1: what the one composition law does to patterns

Over the concrete law of the reference kernel. A composed list is the owner's own patterns followed by the first
occurrence of every name the lifted callees bring, in written reference order, kinds kept (a META capture lifts as an
ordinary binding); a group whose names are all new lifts as itself. `Obligations.composed` says a selected fact IS this
law over the selected reads, so these laws describe every selected signature that carries no X-02 flag.
-/

namespace KatLang.SignatureCompletion

/-- THE SPECIFICATION of the merge over captures: the first occurrence of each name that neither `existing` nor an
    enclosing binding holds, in order, as the caller binding it becomes. -/
def firstNew (forwardable : List Ident) : List CallableParameter → List Ident → List CallableParameter
  | [], _ => []
  | parameter :: rest, existing =>
      if forwardable.contains parameter.name || existing.contains parameter.name then
        firstNew forwardable rest existing
      else liftedCapture parameter :: firstNew forwardable rest (parameter.name :: existing)

/-- The names known after those captures. -/
def seenAfter (forwardable : List Ident) : List CallableParameter → List Ident → List Ident
  | [], existing => existing
  | parameter :: rest, existing =>
      if forwardable.contains parameter.name || existing.contains parameter.name then
        seenAfter forwardable rest existing
      else seenAfter forwardable rest (parameter.name :: existing)

theorem firstNew_append (forwardable : List Ident) : ∀ (a b : List CallableParameter) (existing : List Ident),
    firstNew forwardable (a ++ b) existing
      = firstNew forwardable a existing ++ firstNew forwardable b (seenAfter forwardable a existing) := by
  intro a
  induction a with
  | nil => intro b existing; rfl
  | cons p ps ih =>
    intro b existing
    simp only [List.cons_append, firstNew, seenAfter]
    split
    · exact ih b existing
    · simp only [List.cons_append]
      rw [ih]

theorem seenAfter_append (forwardable : List Ident) : ∀ (a b : List CallableParameter) (existing : List Ident),
    seenAfter forwardable (a ++ b) existing = seenAfter forwardable b (seenAfter forwardable a existing) := by
  intro a
  induction a with
  | nil => intro b existing; rfl
  | cons p ps ih =>
    intro b existing
    simp only [List.cons_append, seenAfter]
    split <;> exact ih b _

/-- The captures of an optional pattern. -/
def capturesOfOption : Option ParameterPattern → List CallableParameter
  | none => []
  | some pattern => ParameterPattern.captures pattern

private theorem capturesOfList_cons (p : ParameterPattern) (ps : Patterns) :
    ParameterPattern.capturesOfList (p :: ps) = ParameterPattern.captures p ++ ParameterPattern.capturesOfList ps := by
  simp [ParameterPattern.capturesOfList]

private theorem singleton_shape : ∀ {first : ParameterPattern} {rest : Patterns},
    ParameterPattern.isSingletonSequenceItems (first :: rest) = true → rest = [] := by
  intro first rest h
  cases rest with
  | nil => rfl
  | cons x xs =>
    cases first <;> simp [ParameterPattern.isSingletonSequenceItems] at h

private theorem closeGroup_captures (original : ParameterPattern) (rebuild : Patterns → ParameterPattern)
    (isSequence : Bool) (items kept : Patterns)
    (horiginal : ParameterPattern.captures original = ParameterPattern.capturesOfList items)
    (hrebuild : ∀ l, ParameterPattern.captures (rebuild l) = ParameterPattern.capturesOfList l) :
    capturesOfOption (closeGroup original rebuild isSequence items kept) = ParameterPattern.capturesOfList kept := by
  unfold closeGroup
  cases kept with
  | nil => simp [capturesOfOption, ParameterPattern.capturesOfList]
  | cons first rest =>
    simp only
    split
    · rename_i h
      simp only [capturesOfOption]
      rw [horiginal, h]
    · split
      · rename_i h
        have hs : ParameterPattern.isSingletonSequenceItems (first :: rest) = true := by
          simp only [Bool.and_eq_true] at h
          exact h.2
        have := singleton_shape hs
        subst this
        simp [capturesOfOption, ParameterPattern.capturesOfList]
      · simp only [capturesOfOption]
        exact hrebuild _

mutual
  /-- The merge of one pattern is the specification over its captures. -/
  theorem missingPattern_spec (forwardable : List Ident) : ∀ (pattern : ParameterPattern) (existing : List Ident),
      capturesOfOption (missingPattern forwardable pattern existing).1
          = firstNew forwardable (ParameterPattern.captures pattern) existing
      ∧ (missingPattern forwardable pattern existing).2
          = seenAfter forwardable (ParameterPattern.captures pattern) existing
    | .capture parameter, existing => by
        simp only [missingPattern, ParameterPattern.captures, firstNew, seenAfter]
        split <;> simp [capturesOfOption, ParameterPattern.captures]
    | .sequenceValue items, existing => by
        have h := missingItems_spec forwardable items existing
        simp only [missingPattern, ParameterPattern.captures]
        refine ⟨?_, h.2⟩
        rw [closeGroup_captures _ _ _ _ _ (by simp [ParameterPattern.captures]) (by simp [ParameterPattern.captures])]
        exact h.1
    | .listValue items, existing => by
        have h := missingItems_spec forwardable items existing
        simp only [missingPattern, ParameterPattern.captures]
        refine ⟨?_, h.2⟩
        rw [closeGroup_captures _ _ _ _ _ (by simp [ParameterPattern.captures]) (by simp [ParameterPattern.captures])]
        exact h.1
    | .unpacking items, existing => by
        have h := missingItems_spec forwardable items existing
        simp only [missingPattern, ParameterPattern.captures]
        refine ⟨?_, h.2⟩
        rw [closeGroup_captures _ _ _ _ _ (by simp [ParameterPattern.captures]) (by simp [ParameterPattern.captures])]
        exact h.1

  /-- The merge of a list is the specification over its captures. -/
  theorem missingItems_spec (forwardable : List Ident) : ∀ (items : Patterns) (existing : List Ident),
      ParameterPattern.capturesOfList (missingItems forwardable items existing).1
          = firstNew forwardable (ParameterPattern.capturesOfList items) existing
      ∧ (missingItems forwardable items existing).2
          = seenAfter forwardable (ParameterPattern.capturesOfList items) existing
    | [], existing => by simp [missingItems, ParameterPattern.capturesOfList, firstNew, seenAfter]
    | pattern :: rest, existing => by
        have h1 := missingPattern_spec forwardable pattern existing
        have h2 := missingItems_spec forwardable rest (missingPattern forwardable pattern existing).2
        simp only [missingItems, capturesOfList_cons, firstNew_append, seenAfter_append]
        rw [← h1.1, ← h1.2, ← h2.1, ← h2.2]
        constructor
        · cases (missingPattern forwardable pattern existing).1 with
          | none => simp [capturesOfOption]
          | some p => simp [capturesOfOption, capturesOfList_cons]
        · rfl
end

/-- The whole dependency sequence: the first occurrence of each name, across and inside the dependencies alike. -/
theorem appended_captures (forwardable : List Ident) : ∀ (dependencies : List Patterns) (existing : List Ident),
    ParameterPattern.capturesOfList (appended forwardable dependencies existing)
      = firstNew forwardable (dependencies.flatMap ParameterPattern.capturesOfList) existing := by
  intro dependencies
  induction dependencies with
  | nil => intro existing; simp [appended, ParameterPattern.capturesOfList, firstNew]
  | cons d ds ih =>
    intro existing
    have h := missingItems_spec forwardable d existing
    simp only [appended, List.flatMap_cons, firstNew_append]
    rw [← h.1, ← h.2, ← ih]
    generalize missingItems forwardable d existing = pair
    obtain ⟨kept, seen⟩ := pair
    simp only
    induction kept with
    | nil => simp [ParameterPattern.capturesOfList]
    | cons p ps ih2 => simp [capturesOfList_cons, ih2]

/-- THE ORDERED SHAPE OF A COMPOSED SIGNATURE. A fact that carries no X-02 flag is the owner's own list, unchanged and
    first, followed by exactly the specification's captures: written dependency order, first occurrence of a name, Q-04
    bindings excluded, kinds kept. -/
theorem composeFact_ordered (own : Patterns) (forwardable : List Ident) (lifted : List Patterns)
    (h : (composeFact own forwardable lifted).violation = none) :
    own <+: (composeFact own forwardable lifted).patterns
    ∧ ParameterPattern.capturesOfList (composeFact own forwardable lifted).patterns
      = ParameterPattern.capturesOfList own
        ++ firstNew forwardable
            ((lifted.filter fun callee => !canForwardStream own callee).flatMap ParameterPattern.capturesOfList)
            (namesOf own) := by
  have happ := appended_captures forwardable (lifted.filter fun callee => !canForwardStream own callee) (namesOf own)
  have list_append : ∀ a b : Patterns, ParameterPattern.capturesOfList (a ++ b)
      = ParameterPattern.capturesOfList a ++ ParameterPattern.capturesOfList b := by
    intro a b
    induction a with
    | nil => simp [ParameterPattern.capturesOfList]
    | cons x xs ih => simp [capturesOfList_cons, ih]
  unfold composeFact at h ⊢
  simp only at h ⊢
  generalize happended : appended forwardable (lifted.filter fun callee => !canForwardStream own callee) (namesOf own) = added at h happ ⊢
  cases added with
  | nil =>
    simp only
    refine ⟨List.prefix_refl _, ?_⟩
    rw [← happ]
    simp [ParameterPattern.capturesOfList]
  | cons first rest =>
    simp only at h ⊢
    cases hv : ParameterPattern.signatureViolation? (own ++ first :: rest) with
    | some v => rw [hv] at h; cases h
    | none =>
      simp only
      refine ⟨List.prefix_append _ _, ?_⟩
      rw [list_append, happ]

/-- THE LIFTED CALLEES FOLLOW WRITTEN ORDER: the lifted signatures are a subsequence of the signatures the references
    denote, in the references' order. -/
theorem liftedFrom_sublist (opened : Nat → Bool) (look : Nat → Patterns) : ∀ (refs : List Reference) (seen : List Nat),
    (liftedFrom opened look refs seen).Sublist (refs.map fun r => signatureOf look r.target) := by
  intro refs
  induction refs with
  | nil => intro seen; exact List.Sublist.refl _
  | cons r rest ih =>
    intro seen
    simp only [liftedFrom, List.map_cons]
    by_cases ha : r.active opened = true
    · rw [ite_eq_left ha]
      generalize signatureOf look r.target = signature
      by_cases h1 : acceptsZero signature = true
      · rw [ite_eq_left h1]
        exact (ih seen).cons _
      · rw [ite_eq_right h1]
        by_cases h2 : seen.contains r.identity = true
        · rw [ite_eq_left h2]
          exact (ih seen).cons _
        · rw [ite_eq_right h2]
          exact (ih _).cons_cons _
    · rw [ite_eq_right ha]
      exact (ih seen).cons _

mutual
  /-- Whether a pattern lifts as itself once its names are all new: no META capture and no empty group. -/
  def liftsWhole : ParameterPattern → Bool
    | .capture parameter => parameter.kind != .metaRef
    | .sequenceValue items => !items.isEmpty && liftsWholeList items
    | .listValue items => !items.isEmpty && liftsWholeList items
    | .unpacking items => !items.isEmpty && liftsWholeList items

  def liftsWholeList : Patterns → Bool
    | [] => true
    | pattern :: rest => liftsWhole pattern && liftsWholeList rest
end

/-- All the names of a capture list are new, and each occurs once. -/
def freshNames (forwardable : List Ident) (parameters : List CallableParameter) (existing : List Ident) : Prop :=
  (parameters.map (·.name)).Nodup
    ∧ ∀ parameter ∈ parameters, parameter.name ∉ forwardable ∧ parameter.name ∉ existing

private theorem mem_seenAfter {forwardable : List Ident} : ∀ {parameters : List CallableParameter}
    {existing : List Ident} {x : Ident}, x ∈ seenAfter forwardable parameters existing →
    x ∈ existing ∨ x ∈ parameters.map (·.name) := by
  intro parameters
  induction parameters with
  | nil => intro existing x h; exact .inl h
  | cons p ps ih =>
    intro existing x h
    simp only [seenAfter] at h
    split at h
    · rcases ih h with h | h
      · exact .inl h
      · exact .inr (by simp only [List.map_cons]; exact List.mem_cons_of_mem _ h)
    · rcases ih h with h | h
      · rcases List.mem_cons.1 h with e | h
        · exact .inr (by simp [e])
        · exact .inl h
      · exact .inr (by simp only [List.map_cons]; exact List.mem_cons_of_mem _ h)

private theorem fresh_split {forwardable existing : List Ident} {a b : List CallableParameter}
    (h : freshNames forwardable (a ++ b) existing) :
    freshNames forwardable a existing ∧ freshNames forwardable b (seenAfter forwardable a existing) := by
  obtain ⟨hnd, hnew⟩ := h
  rw [List.map_append] at hnd
  have hparts := List.nodup_append.1 hnd
  refine ⟨⟨hparts.1, fun p hp => hnew p (List.mem_append_left _ hp)⟩,
    ⟨hparts.2.1, fun p hp => ⟨(hnew p (List.mem_append_right _ hp)).1, fun hseen => ?_⟩⟩⟩
  rcases mem_seenAfter hseen with hs | hs
  · exact (hnew p (List.mem_append_right _ hp)).2 hs
  · exact hparts.2.2 _ hs _ (List.mem_map_of_mem hp) rfl

private theorem liftedCapture_whole {parameter : CallableParameter} (h : (parameter.kind != .metaRef) = true) :
    liftedCapture parameter = parameter := by
  have : parameter.kind ≠ .metaRef := by simpa using h
  simp [liftedCapture, this]

private theorem closeGroup_whole (original : ParameterPattern) (rebuild : Patterns → ParameterPattern)
    (isSequence : Bool) {items : Patterns} (hne : items ≠ []) :
    closeGroup original rebuild isSequence items items = some original := by
  cases items with
  | nil => exact absurd rfl hne
  | cons first rest => simp [closeGroup]

mutual
  /-- A GROUP LIFTS AS ITSELF: a pattern with no META capture and no empty group, all of whose names are new and distinct,
      is kept whole, grouping and kinds included. -/
  theorem missingPattern_whole (forwardable : List Ident) : ∀ (pattern : ParameterPattern) (existing : List Ident),
      liftsWhole pattern = true → freshNames forwardable (ParameterPattern.captures pattern) existing →
      (missingPattern forwardable pattern existing).1 = some pattern
    | .capture parameter, existing, hw, hf => by
        have hnew := hf.2 parameter (by simp [ParameterPattern.captures])
        have h1 : forwardable.contains parameter.name = false := by simpa using hnew.1
        have h2 : existing.contains parameter.name = false := by simpa using hnew.2
        simp only [missingPattern, h1, h2, Bool.or_false, Bool.false_eq_true, ite_false]
        rw [liftedCapture_whole (by simpa [liftsWhole] using hw)]
    | .sequenceValue items, existing, hw, hf => by
        simp only [liftsWhole, Bool.and_eq_true] at hw
        have hne : items ≠ [] := by simpa using hw.1
        simp only [missingPattern]
        rw [missingItems_whole forwardable items existing hw.2 hf]
        exact closeGroup_whole _ _ _ hne
    | .listValue items, existing, hw, hf => by
        simp only [liftsWhole, Bool.and_eq_true] at hw
        have hne : items ≠ [] := by simpa using hw.1
        simp only [missingPattern]
        rw [missingItems_whole forwardable items existing hw.2 hf]
        exact closeGroup_whole _ _ _ hne
    | .unpacking items, existing, hw, hf => by
        simp only [liftsWhole, Bool.and_eq_true] at hw
        have hne : items ≠ [] := by simpa using hw.1
        simp only [missingPattern]
        rw [missingItems_whole forwardable items existing hw.2 hf]
        exact closeGroup_whole _ _ _ hne

  theorem missingItems_whole (forwardable : List Ident) : ∀ (items : Patterns) (existing : List Ident),
      liftsWholeList items = true → freshNames forwardable (ParameterPattern.capturesOfList items) existing →
      (missingItems forwardable items existing).1 = items
    | [], _, _, _ => rfl
    | pattern :: rest, existing, hw, hf => by
        simp only [liftsWholeList, Bool.and_eq_true] at hw
        rw [capturesOfList_cons] at hf
        obtain ⟨hf1, hf2⟩ := fresh_split hf
        have h1 := missingPattern_whole forwardable pattern existing hw.1 hf1
        have hseen := (missingPattern_spec forwardable pattern existing).2
        rw [← hseen] at hf2
        have h2 := missingItems_whole forwardable rest _ hw.2 hf2
        simp only [missingItems]
        rw [h1]
        simp only
        rw [h2]
end

end KatLang.SignatureCompletion
