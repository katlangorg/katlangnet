import KatLangArityLaws.RepeatedNameLaws
import KatLangArityLaws.FamilyDispatch

open KatLang KatLang.BinderTrace

/-!
# Pattern helper laws (R3′, October 2026)

FORMAL-07's roadmap item R3′ (`artifacts/validation/formal07-research/formalization-roadmap.md`,
local; NOT the 2026-10-14 repeated-spread task that reused the label) asked for the pure helpers
the total Model-C binder reaches to become ordinary total definitions, so that literal matching,
the structural kind-mismatch payload and the duplicate-clause check are kernel terms rather than
opaque `partial` constants. Since R3′ every one of them is structural recursion over finite
pattern or value syntax in `lean/KatLang.lean`, written with explicit list walkers instead of
`map`/`flatMap`/`mapM`/a local `go`:

| Family | Total definitions | List walker |
|---|---|---|
| traversal, rendering | `ParameterPattern.captures`, `ParameterPattern.displayName` | `capturesOfList`, `displayNames` |
| conversion | `Pattern.parameterPattern?` (and the now non-recursive `plainClauseParameterPatterns?`) | `parameterPatternsOf?` |
| duplicate comparison | `Pattern.matchEquivalentWithRenaming` (and the wrapper `matchEquivalentItemsWithRenaming`) | `matchEquivalentPairsWithRenaming` |
| value diagnostics | `resultDiagnosticString` | `resultDiagnosticStrings` |
| value matching | `matchPatternInto` (and the wrapper `matchStructureInto`) | `matchItemsInto` |

This module proves, with no premise beyond the ones written:

* § Equations — every walker IS its former higher-order form (`capturesOfList_eq_flatMap`,
  `displayNames_eq_map`, `parameterPatternsOf?_eq_mapM`, `resultDiagnosticStrings_eq_map`,
  `matchEquivalentPairs_eq_foldlM_zip`), so each definition satisfies its former recurrence
  constructor by constructor (`*_old_recurrence`); the old `partial` constants were opaque, so
  "equal to the old constant" is NOT a theorem — preservation is these equations plus the
  bounded executable comparison against verbatim frozen copies
  (`experimental/features/r3prime-pattern-helper-totalization.md`);
* § Conversion — the clause-to-ordinary eligibility boundary is exactly literal-freedom, and a
  converted pattern is the SAME binder head (`parameterPattern?_ofParameter`,
  `plain_clause_head_is_the_need_head`);
* § Rendering — exact text, nested captures, META/collecting spellings and the delimiter-free
  unpacking display; `operandDescription` and `structuralPatternKindMismatch` payloads;
* § Matching — literal success iff the same constructor and payload, fresh/repeated binder
  equations, kind and cardinality rejection, left-to-right accumulation, and that a success
  keeps the incoming environment as a prefix and appends only fresh, distinct names;
* § Renaming — the seeded lookup/extension/failure equations, preservation of a well-formed
  (injective) renaming table, and the STRUCTURAL CHARACTERIZATION of the closed comparison
  (`isMatchEquivalent_iff`): two patterns are match-equivalent exactly when one is the other
  under an injective binder renaming defined on all its binders — structural equality up to
  consistent renaming, never equivalence of the matched value sets;
* § Production — the binder's literal arm at each literal constructor, the binder's kind-mismatch
  error as an explicit string, and the dispatcher's duplicate rejection from a pair of renamed
  heads.

Not claimed: anything about recursive VALUE demand (the production theorems take the demand's
observed outcome as a hypothesis), the repeated-name binder's emitted-count and CALLABLE checks
(`bindName`; the value matcher is NOT that binder), rollback of evaluator state on a pure `none`
(C#'s mutable accumulator may keep a partial prefix), a numeric-representation theorem relating
Lean `Int` text to C# Decimal128 text, or anything about C#.
-/

namespace KatLang.PatternHelpers

/-! ## Equations: the walkers are the former higher-order forms -/

mutual
  theorem capturesOfList_eq_flatMap : (ps : List ParameterPattern) →
      ParameterPattern.capturesOfList ps = ps.flatMap ParameterPattern.captures
    | [] => rfl
    | p :: rest => by
        simp only [ParameterPattern.capturesOfList, List.flatMap_cons, capturesOfList_eq_flatMap rest]
end

/-- `captures` satisfies the former `partial` recurrence, constructor by constructor. -/
theorem captures_old_recurrence (p : ParameterPattern) :
    p.captures = match p with
      | .capture parameter => [parameter]
      | .sequenceValue items => items.flatMap ParameterPattern.captures
      | .listValue items => items.flatMap ParameterPattern.captures
      | .unpacking items => items.flatMap ParameterPattern.captures := by
  cases p <;> simp [ParameterPattern.captures, capturesOfList_eq_flatMap]

theorem capturesOfList_append (ps qs : List ParameterPattern) :
    ParameterPattern.capturesOfList (ps ++ qs)
      = ParameterPattern.capturesOfList ps ++ ParameterPattern.capturesOfList qs := by
  simp [capturesOfList_eq_flatMap]

theorem displayNames_eq_map : (ps : List ParameterPattern) →
    ParameterPattern.displayNames ps = ps.map ParameterPattern.displayName
  | [] => rfl
  | p :: rest => by simp [ParameterPattern.displayNames, displayNames_eq_map rest]

/-- `displayName` satisfies the former `partial` recurrence, constructor by constructor. -/
theorem displayName_old_recurrence (p : ParameterPattern) :
    p.displayName = match p with
      | .capture parameter => parameter.displayName
      | .sequenceValue items => "(" ++ String.intercalate ", " (items.map ParameterPattern.displayName) ++ ")"
      | .listValue items => "[" ++ String.intercalate ", " (items.map ParameterPattern.displayName) ++ "]"
      | .unpacking items => String.intercalate ", " (items.map ParameterPattern.displayName) := by
  cases p <;> simp [ParameterPattern.displayName, displayNames_eq_map]

theorem parameterPatternsOf?_eq_mapM : (ps : List Pattern) →
    Pattern.parameterPatternsOf? ps = ps.mapM Pattern.parameterPattern?
  | [] => rfl
  | p :: rest => by
      simp only [Pattern.parameterPatternsOf?, List.mapM_cons, parameterPatternsOf?_eq_mapM rest]
      rfl

/-- `parameterPattern?` satisfies the former `partial` recurrence, constructor by constructor. -/
theorem parameterPattern?_old_recurrence (p : Pattern) :
    p.parameterPattern? = match p with
      | .bind x => some (.capture { name := x })
      | .sequenceValue ps => do
          let patterns <- ps.mapM Pattern.parameterPattern?
          some (.sequenceValue patterns)
      | .listValue ps => do
          let patterns <- ps.mapM Pattern.parameterPattern?
          some (.listValue patterns)
      | _ => none := by
  cases p <;> simp [Pattern.parameterPattern?, parameterPatternsOf?_eq_mapM]

/-- `plainClauseParameterPatterns?` is its former body (its outer list is the head's own
    argument list, never wrapped; a top-level list pattern is ONE structural argument). -/
theorem plainClauseParameterPatterns?_old_body (p : Pattern) :
    p.plainClauseParameterPatterns? = match p with
      | .bind x => some [.capture { name := x }]
      | .sequenceValue ps => ps.mapM Pattern.parameterPattern?
      | .listValue ps => (Pattern.parameterPattern? (.listValue ps)).map (fun pattern => [pattern])
      | _ => none := by
  cases p <;> simp [Pattern.plainClauseParameterPatterns?, parameterPatternsOf?_eq_mapM]

theorem resultDiagnosticStrings_eq_map : (rs : List Result) →
    resultDiagnosticStrings rs = rs.map resultDiagnosticString
  | [] => rfl
  | r :: rest => by simp [resultDiagnosticStrings, resultDiagnosticStrings_eq_map rest]

/-- `resultDiagnosticString` satisfies the former `partial` recurrence, constructor by
    constructor. -/
theorem resultDiagnosticString_old_recurrence (r : Result) :
    resultDiagnosticString r = match r with
      | .atom value => toString value
      | .str value => "'" ++ value ++ "'"
      | .bool value => Result.boolText value
      | .sequenceValue items => "(" ++ String.intercalate ", " (items.map resultDiagnosticString) ++ ")"
      | .listValue items => "[" ++ String.intercalate ", " (items.map resultDiagnosticString) ++ "]"
      | .callRef _ => "a call reference"
      | .argView _ => "an argument view" := by
  cases r <;> simp [resultDiagnosticString, resultDiagnosticStrings_eq_map]

/-! ## Conversion: the clause-to-ordinary eligibility boundary -/

mutual
  /-- A converted pattern is the SAME binder pattern: the ordinary need pattern of the
      conversion is the clause's own need pattern (kind, nesting and order preserved). -/
  theorem parameterPattern?_ofParameter : (p : Pattern) → (q : ParameterPattern) →
      p.parameterPattern? = some q → NeedPattern.ofParameter q = NeedPattern.ofClause p
    | .bind x, q, h => by
        simp only [Pattern.parameterPattern?, Option.some.injEq] at h
        subst h; simp [NeedPattern.ofParameter, NeedPattern.ofClause]
    | .litInt _, _, h => by simp [Pattern.parameterPattern?] at h
    | .litString _, _, h => by simp [Pattern.parameterPattern?] at h
    | .litBool _, _, h => by simp [Pattern.parameterPattern?] at h
    | .sequenceValue ps, q, h => by
        simp only [Pattern.parameterPattern?, Option.bind_eq_bind, Option.bind_eq_some_iff,
          Option.some.injEq] at h
        obtain ⟨qs, hqs, rfl⟩ := h
        simp only [NeedPattern.ofParameter, NeedPattern.ofClause, parameterPatternsOf?_ofParameter ps qs hqs]
    | .listValue ps, q, h => by
        simp only [Pattern.parameterPattern?, Option.bind_eq_bind, Option.bind_eq_some_iff,
          Option.some.injEq] at h
        obtain ⟨qs, hqs, rfl⟩ := h
        simp only [NeedPattern.ofParameter, NeedPattern.ofClause, parameterPatternsOf?_ofParameter ps qs hqs]

  theorem parameterPatternsOf?_ofParameter : (ps : List Pattern) → (qs : List ParameterPattern) →
      Pattern.parameterPatternsOf? ps = some qs → qs.map NeedPattern.ofParameter = ps.map NeedPattern.ofClause
    | [], qs, h => by
        simp only [Pattern.parameterPatternsOf?, Option.some.injEq] at h
        subst h; rfl
    | p :: rest, qs, h => by
        simp only [Pattern.parameterPatternsOf?, Option.bind_eq_bind, Option.bind_eq_some_iff,
          Option.some.injEq] at h
        obtain ⟨q, hq, qs', hqs', rfl⟩ := h
        simp only [List.map_cons, parameterPattern?_ofParameter p q hq,
          parameterPatternsOf?_ofParameter rest qs' hqs']
end

mutual
  /-- THE ELIGIBILITY BOUNDARY: a clause pattern converts to an ordinary parameter pattern
      exactly when it contains no literal at any depth. -/
  theorem parameterPattern?_isSome : (p : Pattern) →
      (p.parameterPattern?).isSome = (NeedPattern.ofClause p).literalFree
    | .bind _ => by simp [Pattern.parameterPattern?, NeedPattern.ofClause, NeedPattern.literalFree]
    | .litInt _ => by simp [Pattern.parameterPattern?, NeedPattern.ofClause, NeedPattern.literalFree]
    | .litString _ => by simp [Pattern.parameterPattern?, NeedPattern.ofClause, NeedPattern.literalFree]
    | .litBool _ => by simp [Pattern.parameterPattern?, NeedPattern.ofClause, NeedPattern.literalFree]
    | .sequenceValue ps => by
        have := parameterPatternsOf?_isSome ps
        simp only [Pattern.parameterPattern?, NeedPattern.ofClause, NeedPattern.literalFree]
        cases h : Pattern.parameterPatternsOf? ps <;> simp_all
    | .listValue ps => by
        have := parameterPatternsOf?_isSome ps
        simp only [Pattern.parameterPattern?, NeedPattern.ofClause, NeedPattern.literalFree]
        cases h : Pattern.parameterPatternsOf? ps <;> simp_all

  theorem parameterPatternsOf?_isSome : (ps : List Pattern) →
      (Pattern.parameterPatternsOf? ps).isSome
        = BinderCorrespondence.literalFreeList (ps.map NeedPattern.ofClause)
    | [] => rfl
    | p :: rest => by
        have h1 := parameterPattern?_isSome p
        have h2 := parameterPatternsOf?_isSome rest
        simp only [Pattern.parameterPatternsOf?, List.map_cons, BinderCorrespondence.literalFreeList]
        cases hp : p.parameterPattern? <;> cases hr : Pattern.parameterPatternsOf? rest <;> simp_all
end

/-- An eligible sole clause head IS the binder head the clause family would use: converting a
    clause to an ordinary signature changes no pattern the binder sees. The outer argument list
    stays the head's own list (`needClauseHead` opens it), a top-level list pattern stays ONE
    structural argument. -/
theorem plain_clause_head_is_the_need_head (p : Pattern) (qs : List ParameterPattern)
    (h : p.plainClauseParameterPatterns? = some qs) :
    qs.map NeedPattern.ofParameter = needClauseHead p := by
  cases p with
  | bind x =>
      simp only [Pattern.plainClauseParameterPatterns?, Option.some.injEq] at h
      subst h; simp [NeedPattern.ofParameter, NeedPattern.ofClause, needClauseHead]
  | sequenceValue ps =>
      exact parameterPatternsOf?_ofParameter ps qs h
  | listValue ps =>
      simp only [Pattern.plainClauseParameterPatterns?, Option.map_eq_some_iff] at h
      obtain ⟨q, hq, rfl⟩ := h
      simp only [List.map_cons, List.map_nil, needClauseHead, parameterPattern?_ofParameter _ q hq]
  | litInt _ => simp [Pattern.plainClauseParameterPatterns?] at h
  | litString _ => simp [Pattern.plainClauseParameterPatterns?] at h
  | litBool _ => simp [Pattern.plainClauseParameterPatterns?] at h

/-- Sole clause heads with a literal at any depth are never ordinary-eligible. -/
theorem plain_clause_eligible_iff (p : Pattern) :
    (p.plainClauseParameterPatterns?).isSome
      = BinderCorrespondence.literalFreeList (needClauseHead p) := by
  cases p with
  | bind _ => simp [Pattern.plainClauseParameterPatterns?, needClauseHead, NeedPattern.ofClause, NeedPattern.literalFree, BinderCorrespondence.literalFreeList]
  | litInt _ => simp [Pattern.plainClauseParameterPatterns?, needClauseHead, NeedPattern.ofClause, NeedPattern.literalFree, BinderCorrespondence.literalFreeList]
  | litString _ => simp [Pattern.plainClauseParameterPatterns?, needClauseHead, NeedPattern.ofClause, NeedPattern.literalFree, BinderCorrespondence.literalFreeList]
  | litBool _ => simp [Pattern.plainClauseParameterPatterns?, needClauseHead, NeedPattern.ofClause, NeedPattern.literalFree, BinderCorrespondence.literalFreeList]
  | sequenceValue ps => exact parameterPatternsOf?_isSome ps
  | listValue ps =>
      have := parameterPattern?_isSome (.listValue ps)
      simp only [Pattern.plainClauseParameterPatterns?, Option.isSome_map, needClauseHead,
        BinderCorrespondence.literalFreeList, Bool.and_true]
      exact this

mutual
  /-- CAPTURE ORDER AND KIND: a converted pattern's captures are the clause's binders in
      written order, repeated names kept, every one an ordinary (non-collecting, non-META)
      capture. -/
  theorem parameterPattern?_captures : (p : Pattern) → (q : ParameterPattern) →
      p.parameterPattern? = some q → q.captures = p.boundNames.map (fun x => { name := x })
    | .bind x, q, h => by
        simp only [Pattern.parameterPattern?, Option.some.injEq] at h
        subst h; simp [ParameterPattern.captures, Pattern.boundNames]
    | .litInt _, _, h => by simp [Pattern.parameterPattern?] at h
    | .litString _, _, h => by simp [Pattern.parameterPattern?] at h
    | .litBool _, _, h => by simp [Pattern.parameterPattern?] at h
    | .sequenceValue ps, q, h => by
        simp only [Pattern.parameterPattern?, Option.bind_eq_bind, Option.bind_eq_some_iff,
          Option.some.injEq] at h
        obtain ⟨qs, hqs, rfl⟩ := h
        simp only [ParameterPattern.captures, Pattern.boundNames, parameterPatternsOf?_captures ps qs hqs]
    | .listValue ps, q, h => by
        simp only [Pattern.parameterPattern?, Option.bind_eq_bind, Option.bind_eq_some_iff,
          Option.some.injEq] at h
        obtain ⟨qs, hqs, rfl⟩ := h
        simp only [ParameterPattern.captures, Pattern.boundNames, parameterPatternsOf?_captures ps qs hqs]

  theorem parameterPatternsOf?_captures : (ps : List Pattern) → (qs : List ParameterPattern) →
      Pattern.parameterPatternsOf? ps = some qs →
        ParameterPattern.capturesOfList qs = (ps.flatMap Pattern.boundNames).map (fun x => { name := x })
    | [], qs, h => by
        simp only [Pattern.parameterPatternsOf?, Option.some.injEq] at h
        subst h; rfl
    | p :: rest, qs, h => by
        simp only [Pattern.parameterPatternsOf?, Option.bind_eq_bind, Option.bind_eq_some_iff,
          Option.some.injEq] at h
        obtain ⟨q, hq, qs', hqs', rfl⟩ := h
        simp only [ParameterPattern.capturesOfList, parameterPattern?_captures p q hq,
          parameterPatternsOf?_captures rest qs' hqs', List.flatMap_cons, List.map_append]
end

/-- The names an eligible sole clause head declares are its binders in written order. -/
theorem plainClauseParamNames?_eq_boundNames (p : Pattern) (names : List Ident)
    (h : p.plainClauseParamNames? = some names) : names = p.boundNames := by
  simp only [Pattern.plainClauseParamNames?, Option.map_eq_some_iff] at h
  obtain ⟨qs, hqs, rfl⟩ := h
  cases p with
  | bind x =>
      simp only [Pattern.plainClauseParameterPatterns?, Option.some.injEq] at hqs
      subst hqs; simp [ParameterPattern.captures, Pattern.boundNames]
  | sequenceValue ps =>
      simp only [Pattern.plainClauseParameterPatterns?] at hqs
      rw [← capturesOfList_eq_flatMap, parameterPatternsOf?_captures ps qs hqs]
      simp [Pattern.boundNames, Function.comp_def]
  | listValue ps =>
      simp only [Pattern.plainClauseParameterPatterns?, Option.map_eq_some_iff] at hqs
      obtain ⟨q, hq, rfl⟩ := hqs
      simp [parameterPattern?_captures _ q hq, Function.comp_def]
  | litInt _ => simp [Pattern.plainClauseParameterPatterns?] at hqs
  | litString _ => simp [Pattern.plainClauseParameterPatterns?] at hqs
  | litBool _ => simp [Pattern.plainClauseParameterPatterns?] at hqs

mutual
  /-- A pattern's captures are the binder names its need pattern binds, in order (the binder's
      `NeedPattern.names`, which decides repeated names). -/
  theorem need_names_are_capture_names : (p : ParameterPattern) →
      (NeedPattern.ofParameter p).names = p.captures.map CallableParameter.name
    | .capture parameter => by
        cases parameter with
        | mk name kind => cases kind <;> simp [NeedPattern.ofParameter, NeedPattern.names, ParameterPattern.captures]
    | .sequenceValue items => by
        simp only [NeedPattern.ofParameter, NeedPattern.names, ParameterPattern.captures]
        exact need_names_are_capture_names_list items
    | .listValue items => by
        simp only [NeedPattern.ofParameter, NeedPattern.names, ParameterPattern.captures]
        exact need_names_are_capture_names_list items
    | .unpacking items => by
        simp only [NeedPattern.ofParameter, NeedPattern.names, ParameterPattern.captures]
        exact need_names_are_capture_names_list items

  theorem need_names_are_capture_names_list : (ps : List ParameterPattern) →
      (ps.map NeedPattern.ofParameter).flatMap NeedPattern.names
        = (ParameterPattern.capturesOfList ps).map CallableParameter.name
    | [] => rfl
    | p :: rest => by
        simp only [List.map_cons, List.flatMap_cons, ParameterPattern.capturesOfList, List.map_append,
          need_names_are_capture_names p, need_names_are_capture_names_list rest]
end

/-! ## Rendering: exact diagnostic text -/

theorem displayName_capture (parameter : CallableParameter) :
    (ParameterPattern.capture parameter).displayName = parameter.displayName := rfl

theorem displayName_normal (name : Ident) :
    (ParameterPattern.capture { name := name }).displayName = name := rfl

theorem displayName_collecting (name : Ident) :
    (ParameterPattern.capture { name := name, kind := .collecting }).displayName = "*" ++ name := rfl

theorem displayName_meta (name : Ident) :
    (ParameterPattern.capture { name := name, kind := .metaRef }).displayName = "meta " ++ name := rfl

theorem displayName_sequenceValue (items : List ParameterPattern) :
    (ParameterPattern.sequenceValue items).displayName
      = "(" ++ String.intercalate ", " (items.map ParameterPattern.displayName) ++ ")" := by
  simp [ParameterPattern.displayName, displayNames_eq_map]

theorem displayName_listValue (items : List ParameterPattern) :
    (ParameterPattern.listValue items).displayName
      = "[" ++ String.intercalate ", " (items.map ParameterPattern.displayName) ++ "]" := by
  simp [ParameterPattern.displayName, displayNames_eq_map]

/-- The deconstruction receiver displays its written target list WITHOUT delimiters. -/
theorem displayName_unpacking (items : List ParameterPattern) :
    (ParameterPattern.unpacking items).displayName
      = String.intercalate ", " (items.map ParameterPattern.displayName) := by
  simp [ParameterPattern.displayName, displayNames_eq_map]

/-- The written form of the binder's own structural patterns (`NeedPattern.toParameter`). -/
theorem need_sequence_displayName (ps : List NeedPattern) :
    (NeedPattern.sequence ps).toParameter.displayName
      = "(" ++ String.intercalate ", " ((ps.map NeedPattern.toParameter).map ParameterPattern.displayName) ++ ")" := by
  simp [NeedPattern.toParameter, displayName_sequenceValue]

theorem need_list_displayName (ps : List NeedPattern) :
    (NeedPattern.list ps).toParameter.displayName
      = "[" ++ String.intercalate ", " ((ps.map NeedPattern.toParameter).map ParameterPattern.displayName) ++ "]" := by
  simp [NeedPattern.toParameter, displayName_listValue]

theorem resultDiagnosticString_sequenceValue (items : List Result) :
    resultDiagnosticString (.sequenceValue items)
      = "(" ++ String.intercalate ", " (items.map resultDiagnosticString) ++ ")" := by
  simp [resultDiagnosticString, resultDiagnosticStrings_eq_map]

theorem resultDiagnosticString_listValue (items : List Result) :
    resultDiagnosticString (.listValue items)
      = "[" ++ String.intercalate ", " (items.map resultDiagnosticString) ++ "]" := by
  simp [resultDiagnosticString, resultDiagnosticStrings_eq_map]

/-- A call reference and an argument view render as fixed descriptions, whatever their plan. -/
theorem resultDiagnosticString_callRef (address : Nat) :
    resultDiagnosticString (.callRef address) = "a call reference" := rfl

theorem resultDiagnosticString_argView (address : Nat) :
    resultDiagnosticString (.argView address) = "an argument view" := rfl

/-- A string is quoted with `'` and NOT escaped. -/
theorem resultDiagnosticString_str (value : String) :
    resultDiagnosticString (.str value) = "'" ++ value ++ "'" := rfl

theorem operandDescription_sequenceValue (items : List Result) :
    operandDescription (.sequenceValue items)
      = "a sequence value with " ++ toString items.length ++ " sequence element"
          ++ (if items.length = 1 then "" else "s") ++ ": "
          ++ ("(" ++ String.intercalate ", " (items.map resultDiagnosticString) ++ ")") := by
  rw [← resultDiagnosticString_sequenceValue]; rfl

theorem operandDescription_listValue (items : List Result) :
    operandDescription (.listValue items)
      = "a list value with " ++ toString items.length ++ " element"
          ++ (if items.length = 1 then "" else "s") ++ ": "
          ++ ("[" ++ String.intercalate ", " (items.map resultDiagnosticString) ++ "]") := by
  rw [← resultDiagnosticString_listValue]; rfl

/-- THE KIND-MISMATCH PAYLOAD of a list pattern, for every value (direct calls included). -/
theorem structuralPatternKindMismatch_listValue (items : List ParameterPattern) (value : Result) :
    structuralPatternKindMismatch (.listValue items) value
      = Error.typeMismatch ("list pattern `" ++ (ParameterPattern.listValue items).displayName
          ++ "` expects a list value, but received " ++ operandDescription value) := rfl

/-- Every other pattern — a sequence pattern, and on a direct call outside the binder's domain
    a capture or the unpacking receiver too — is reported as a SEQUENCE pattern. -/
theorem structuralPatternKindMismatch_other (pattern : ParameterPattern) (value : Result)
    (h : ∀ items, pattern ≠ .listValue items) :
    structuralPatternKindMismatch pattern value
      = Error.typeMismatch ("sequence pattern `" ++ pattern.displayName
          ++ "` expects a sequence value, but received " ++ operandDescription value) := by
  cases pattern with
  | listValue items => exact absurd rfl (h items)
  | _ => rfl

/-! ## Matching: the value matcher's contract -/

theorem matchPatternInto_bind (x : Ident) (r : Result) (env : ValEnv) :
    matchPatternInto (.bind x) r env = match env.lookup x with
      | some existing => if existing == r then some env else none
      | none => some (env ++ [(x, r)]) := by
  rfl

/-- A FRESH binder appends exactly one entry, at the end. -/
theorem matchPatternInto_bind_fresh (x : Ident) (r : Result) (env : ValEnv) (h : env.lookup x = none) :
    matchPatternInto (.bind x) r env = some (env ++ [(x, r)]) := by
  simp [matchPatternInto_bind, h]

/-- A REPEATED binder compares with the existing lookup (structural equality, `LawfulBEq`) and
    adds no entry. -/
theorem matchPatternInto_bind_repeated (x : Ident) (r existing : Result) (env : ValEnv)
    (h : env.lookup x = some existing) :
    matchPatternInto (.bind x) r env = if existing == r then some env else none := by
  simp [matchPatternInto_bind, h]

/-- An integer literal matches only a number with that value: no Boolean, string or structure. -/
theorem matchPatternInto_litInt (n : Int) (r : Result) (env : ValEnv) :
    matchPatternInto (.litInt n) r env = if r == .atom n then some env else none := by
  cases r <;> simp [matchPatternInto]

theorem matchPatternInto_litString (s : String) (r : Result) (env : ValEnv) :
    matchPatternInto (.litString s) r env = if r == .str s then some env else none := by
  cases r <;> simp [matchPatternInto]

/-- A Boolean literal matches only that Boolean: there is no numeric truthiness. -/
theorem matchPatternInto_litBool (b : Bool) (r : Result) (env : ValEnv) :
    matchPatternInto (.litBool b) r env = if r == .bool b then some env else none := by
  cases r <;> simp [matchPatternInto]

theorem matchPatternInto_sequenceValue (ps : List Pattern) (r : Result) (env : ValEnv) :
    matchPatternInto (.sequenceValue ps) r env
      = matchStructureInto ps (patternStructureMembers? (Result.sequencePatternItems? r) ps.length) env := by
  simp only [matchPatternInto, matchStructureInto]

theorem matchPatternInto_listValue (ps : List Pattern) (r : Result) (env : ValEnv) :
    matchPatternInto (.listValue ps) r env
      = matchStructureInto ps (patternStructureMembers? (Result.listPatternItems? r) ps.length) env := by
  simp only [matchPatternInto, matchStructureInto]

/-- `matchPatternInto` satisfies its former `partial` body, constructor by constructor. -/
theorem matchPatternInto_old_recurrence (p : Pattern) (r : Result) (env : ValEnv) :
    matchPatternInto p r env = match p with
      | .bind x =>
          match env.lookup x with
          | some existing => if existing == r then some env else none
          | none => some (env ++ [(x, r)])
      | .litInt n => match r with
          | .atom v => if v = n then some env else none
          | _ => none
      | .litString s => match r with
          | .str v => if v = s then some env else none
          | _ => none
      | .litBool b => match r with
          | .bool v => if v = b then some env else none
          | _ => none
      | .sequenceValue ps => matchStructureInto ps (patternStructureMembers? (Result.sequencePatternItems? r) ps.length) env
      | .listValue ps => matchStructureInto ps (patternStructureMembers? (Result.listPatternItems? r) ps.length) env := by
  cases p with
  | sequenceValue ps => exact matchPatternInto_sequenceValue ps r env
  | listValue ps => exact matchPatternInto_listValue ps r env
  | _ => rfl

theorem matchStructureInto_none (ps : List Pattern) (env : ValEnv) :
    matchStructureInto ps none env = none := rfl

theorem matchStructureInto_some (ps : List Pattern) (rs : List Result) (env : ValEnv) :
    matchStructureInto ps (some rs) env = matchItemsInto ps rs env := rfl

/-- The item walker's equations ARE the former local `go` of `matchStructureInto`. -/
theorem matchItemsInto_nil (env : ValEnv) : matchItemsInto [] [] env = some env := by
  simp [matchItemsInto]

theorem matchItemsInto_cons (p : Pattern) (ps : List Pattern) (r : Result) (rs : List Result) (env : ValEnv) :
    matchItemsInto (p :: ps) (r :: rs) env
      = (matchPatternInto p r env).bind (fun next => matchItemsInto ps rs next) := by
  simp only [matchItemsInto]; rfl

theorem matchItemsInto_nil_cons (r : Result) (rs : List Result) (env : ValEnv) :
    matchItemsInto [] (r :: rs) env = none := by simp [matchItemsInto]

theorem matchItemsInto_cons_nil (p : Pattern) (ps : List Pattern) (env : ValEnv) :
    matchItemsInto (p :: ps) [] env = none := by simp [matchItemsInto]

/-- The direct structure helper keeps every distinction: no members, and items of a different
    count, are both `none` — even past a matching prefix. -/
theorem matchItemsInto_length {ps : List Pattern} {rs : List Result} {env out : ValEnv}
    (h : matchItemsInto ps rs env = some out) : ps.length = rs.length := by
  induction ps generalizing rs env with
  | nil => cases rs with
    | nil => rfl
    | cons _ _ => simp [matchItemsInto] at h
  | cons p ps ih => cases rs with
    | nil => simp [matchItemsInto] at h
    | cons r rs =>
        rw [matchItemsInto_cons, Option.bind_eq_some_iff] at h
        obtain ⟨next, _, h2⟩ := h
        simp [ih h2]

/-- KIND REJECTION: a sequence pattern never opens a value that is not a sequence (a list, a
    scalar, a call reference, an argument view), whatever its items. -/
theorem matchPatternInto_sequence_wrong_kind (ps : List Pattern) (r : Result) (env : ValEnv)
    (h : Result.sequencePatternItems? r = none) : matchPatternInto (.sequenceValue ps) r env = none := by
  simp [matchPatternInto_sequenceValue, h, patternStructureMembers?, matchStructureInto]

theorem matchPatternInto_list_wrong_kind (ps : List Pattern) (r : Result) (env : ValEnv)
    (h : Result.listPatternItems? r = none) : matchPatternInto (.listValue ps) r env = none := by
  simp [matchPatternInto_listValue, h, patternStructureMembers?, matchStructureInto]

/-- CARDINALITY: a right-kind value opens only with exactly as many items as the pattern. -/
theorem matchPatternInto_sequence_items (ps : List Pattern) (rs : List Result) (env : ValEnv) :
    matchPatternInto (.sequenceValue ps) (.sequenceValue rs) env
      = if rs.length = ps.length then matchItemsInto ps rs env else none := by
  simp only [matchPatternInto_sequenceValue, Result.sequencePatternItems?, patternStructureMembers?,
    beq_iff_eq]
  split <;> rfl

theorem matchPatternInto_list_items (ps : List Pattern) (rs : List Result) (env : ValEnv) :
    matchPatternInto (.listValue ps) (.listValue rs) env
      = if rs.length = ps.length then matchItemsInto ps rs env else none := by
  simp only [matchPatternInto_listValue, Result.listPatternItems?, patternStructureMembers?,
    beq_iff_eq]
  split <;> rfl

/-- RAW INPUTS keep their current results: source admission rejects a one-item sequence
    pattern, but the matcher itself opens a raw one-item sequence value like any other, and
    never adapts a non-sequence to it. -/
theorem matchPatternInto_raw_singleton (p : Pattern) (r : Result) (env : ValEnv) :
    matchPatternInto (.sequenceValue [p]) (.sequenceValue [r]) env = matchPatternInto p r env := by
  rw [matchPatternInto_sequence_items]
  simp only [List.length_cons, List.length_nil, ↓reduceIte, matchItemsInto_cons]
  cases matchPatternInto p r env <;> simp [matchItemsInto_nil]

theorem lookupAssoc_eq_none_iff {A : Type} (x : Ident) (l : Assoc Ident A) :
    lookupAssoc x l = none ↔ x ∉ l.map Prod.fst := by
  induction l with
  | nil => simp [lookupAssoc]
  | cons head tail ih =>
    obtain ⟨key, value⟩ := head
    by_cases hx : x = key
    · subst hx; simp [lookupAssoc]
    · simp [lookupAssoc, hx, ih]

/-- What a successful match adds: the incoming environment is kept as a PREFIX, and the
    appended entries are names that were unbound in it, each appended once. -/
def Appends (env out : ValEnv) : Prop :=
  ∃ added, out = env ++ added ∧ (∀ x ∈ added.map Prod.fst, env.lookup x = none)
    ∧ (added.map Prod.fst).Nodup

theorem appends_refl (env : ValEnv) : Appends env env :=
  ⟨[], by simp, by simp, by simp⟩

theorem appends_trans {a b c : ValEnv} (h1 : Appends a b) (h2 : Appends b c) : Appends a c := by
  obtain ⟨d1, rfl, f1, n1⟩ := h1
  obtain ⟨d2, rfl, f2, n2⟩ := h2
  refine ⟨d1 ++ d2, by simp, ?_, ?_⟩
  · intro x hx
    simp only [List.map_append, List.mem_append] at hx
    rcases hx with hx | hx
    · exact f1 x hx
    · have h := f2 x hx
      simp only [ValEnv.lookup] at h ⊢
      rw [FamilyDispatch.lookupAssoc_append] at h
      cases hq : lookupAssoc x a with
      | none => rfl
      | some v => rw [hq] at h; cases h
  · rw [List.map_append, List.nodup_append]
    refine ⟨n1, n2, ?_⟩
    intro x hx y hy hxy
    subst hxy
    have h := f2 x hy
    simp only [ValEnv.lookup] at h
    rw [FamilyDispatch.lookupAssoc_append] at h
    have hnone : lookupAssoc x d1 = none := by
      cases hq : lookupAssoc x a with
      | none => rw [hq] at h; exact h
      | some v => rw [hq] at h; cases h
    exact (lookupAssoc_eq_none_iff x d1).1 hnone hx

mutual
  /-- ORDERED ACCUMULATION: a successful match keeps the incoming environment — duplicates and
      precedence included — as a prefix and appends only names that were unbound in it, each
      once, for every incoming environment. -/
  theorem matchPatternInto_appends : (p : Pattern) → (r : Result) → (env out : ValEnv) →
      matchPatternInto p r env = some out → Appends env out
    | .bind x, r, env, out, h => by
        rw [matchPatternInto_bind] at h
        cases hl : env.lookup x with
        | some existing =>
            simp only [hl] at h
            split at h
            · cases h; exact appends_refl env
            · cases h
        | none =>
            simp only [hl, Option.some.injEq] at h
            subst h
            exact ⟨[(x, r)], rfl, by simpa using hl, by simp⟩
    | .litInt n, r, env, out, h => by
        rw [matchPatternInto_litInt] at h
        split at h
        · cases h; exact appends_refl env
        · cases h
    | .litString s, r, env, out, h => by
        rw [matchPatternInto_litString] at h
        split at h
        · cases h; exact appends_refl env
        · cases h
    | .litBool b, r, env, out, h => by
        rw [matchPatternInto_litBool] at h
        split at h
        · cases h; exact appends_refl env
        · cases h
    | .sequenceValue ps, r, env, out, h => by
        rw [matchPatternInto_sequenceValue] at h
        cases hm : patternStructureMembers? (Result.sequencePatternItems? r) ps.length with
        | none => rw [hm] at h; cases h
        | some rs => rw [hm, matchStructureInto_some] at h; exact matchItemsInto_appends ps rs env out h
    | .listValue ps, r, env, out, h => by
        rw [matchPatternInto_listValue] at h
        cases hm : patternStructureMembers? (Result.listPatternItems? r) ps.length with
        | none => rw [hm] at h; cases h
        | some rs => rw [hm, matchStructureInto_some] at h; exact matchItemsInto_appends ps rs env out h

  theorem matchItemsInto_appends : (ps : List Pattern) → (rs : List Result) → (env out : ValEnv) →
      matchItemsInto ps rs env = some out → Appends env out
    | [], [], env, out, h => by
        rw [matchItemsInto_nil] at h; cases h; exact appends_refl env
    | [], _ :: _, _, _, h => by rw [matchItemsInto_nil_cons] at h; cases h
    | _ :: _, [], _, _, h => by rw [matchItemsInto_cons_nil] at h; cases h
    | p :: ps, r :: rs, env, out, h => by
        rw [matchItemsInto_cons, Option.bind_eq_some_iff] at h
        obtain ⟨next, h1, h2⟩ := h
        exact appends_trans (matchPatternInto_appends p r env next h1)
          (matchItemsInto_appends ps rs next out h2)
end

/-- Every binding of the incoming environment is still what lookup finds after a success. -/
theorem matchPatternInto_preserves_lookup {p : Pattern} {r : Result} {env out : ValEnv}
    (h : matchPatternInto p r env = some out) {x : Ident} {v : Result} (hx : env.lookup x = some v) :
    out.lookup x = some v := by
  obtain ⟨added, rfl, _, _⟩ := matchPatternInto_appends p r env out h
  simp only [ValEnv.lookup] at hx ⊢
  rw [FamilyDispatch.lookupAssoc_append, hx]

/-- Under the explicit premise that the incoming environment has distinct names, a success has
    distinct names too (in particular every `matchPattern` result does). -/
theorem matchPatternInto_nodup {p : Pattern} {r : Result} {env out : ValEnv}
    (h : matchPatternInto p r env = some out) (hn : (env.map Prod.fst).Nodup) :
    (out.map Prod.fst).Nodup := by
  obtain ⟨added, rfl, hf, hna⟩ := matchPatternInto_appends p r env out h
  rw [List.map_append, List.nodup_append]
  refine ⟨hn, hna, ?_⟩
  intro x hx y hy hxy
  subst hxy
  exact (lookupAssoc_eq_none_iff x env).1 (hf x hy) hx

theorem matchPattern_nodup {p : Pattern} {r : Result} {out : ValEnv}
    (h : matchPattern p r = some out) : (out.map Prod.fst).Nodup :=
  matchPatternInto_nodup h (by simp)

/-- A literal binds nothing: its success returns the incoming environment unchanged. -/
theorem matchPattern_literal_isSome (r : Result) :
    ((matchPattern (.litInt n) r).isSome = true ↔ r = .atom n)
    ∧ ((matchPattern (.litString s) r).isSome = true ↔ r = .str s)
    ∧ ((matchPattern (.litBool b) r).isSome = true ↔ r = .bool b) := by
  simp only [matchPattern, matchPatternInto_litInt, matchPatternInto_litString, matchPatternInto_litBool]
  refine ⟨?_, ?_, ?_⟩ <;> split <;> simp_all

/-! ## Renaming: duplicate-pattern comparison -/

section Renaming

open Pattern

/-! ### The seeded equations -/

/-- A left binder already in the table must meet its recorded right name. -/
theorem equiv_bind_known (left right existing : Ident) (pairs : List (Ident × Ident))
    (h : binderRenaming? left pairs = some existing) :
    matchEquivalentWithRenaming (.bind left) (.bind right) pairs
      = if existing = right then some pairs else none := by
  simp [matchEquivalentWithRenaming, h]

/-- A NEW left binder may not reuse a right name the table already targets. -/
theorem equiv_bind_reused_target (left right : Ident) (pairs : List (Ident × Ident))
    (h : binderRenaming? left pairs = none) (hu : binderTargetUsed right pairs = true) :
    matchEquivalentWithRenaming (.bind left) (.bind right) pairs = none := by
  simp [matchEquivalentWithRenaming, h, hu]

/-- A new left binder with an unused right name PREPENDS its pair. -/
theorem equiv_bind_new (left right : Ident) (pairs : List (Ident × Ident))
    (h : binderRenaming? left pairs = none) (hu : binderTargetUsed right pairs = false) :
    matchEquivalentWithRenaming (.bind left) (.bind right) pairs = some ((left, right) :: pairs) := by
  simp [matchEquivalentWithRenaming, h, hu]

theorem equiv_litInt (m n : Int) (pairs : List (Ident × Ident)) :
    matchEquivalentWithRenaming (.litInt m) (.litInt n) pairs = if m = n then some pairs else none := rfl

theorem equiv_litString (s t : String) (pairs : List (Ident × Ident)) :
    matchEquivalentWithRenaming (.litString s) (.litString t) pairs = if s = t then some pairs else none := rfl

theorem equiv_litBool (b c : Bool) (pairs : List (Ident × Ident)) :
    matchEquivalentWithRenaming (.litBool b) (.litBool c) pairs = if b = c then some pairs else none := rfl

theorem matchEquivalent_sequenceValue (ps qs : List Pattern) (pairs : List (Ident × Ident)) :
    matchEquivalentWithRenaming (.sequenceValue ps) (.sequenceValue qs) pairs
      = matchEquivalentItemsWithRenaming ps qs pairs := rfl

theorem matchEquivalent_listValue (ps qs : List Pattern) (pairs : List (Ident × Ident)) :
    matchEquivalentWithRenaming (.listValue ps) (.listValue qs) pairs
      = matchEquivalentItemsWithRenaming ps qs pairs := rfl

/-- The structural KIND is part of the shape: a sequence pattern never meets a list pattern. -/
theorem equiv_sequence_list (ps qs : List Pattern) (pairs : List (Ident × Ident)) :
    matchEquivalentWithRenaming (.sequenceValue ps) (.listValue qs) pairs = none
    ∧ matchEquivalentWithRenaming (.listValue ps) (.sequenceValue qs) pairs = none :=
  ⟨rfl, rfl⟩

theorem equivItems_length (ps qs : List Pattern) (pairs : List (Ident × Ident)) (h : ps.length ≠ qs.length) :
    matchEquivalentItemsWithRenaming ps qs pairs = none := by
  simp [matchEquivalentItemsWithRenaming, h]

/-- The lockstep walker IS the former local `go` over `ps.zip qs` (a left fold in `Option`). -/
theorem matchEquivalentPairs_eq_foldlM_zip : (ps qs : List Pattern) → (pairs : List (Ident × Ident)) →
    ps.length = qs.length →
    matchEquivalentPairsWithRenaming ps qs pairs
      = (ps.zip qs).foldlM (fun current pq => matchEquivalentWithRenaming pq.1 pq.2 current) pairs
  | [], [], _, _ => by simp [matchEquivalentPairsWithRenaming]
  | [], _ :: _, _, h => by simp at h
  | _ :: _, [], _, h => by simp at h
  | p :: ps, q :: qs, pairs, h => by
      simp only [List.length_cons, Nat.add_right_cancel_iff] at h
      simp only [matchEquivalentPairsWithRenaming, List.zip_cons_cons, List.foldlM_cons]
      cases matchEquivalentWithRenaming p q pairs with
      | none => rfl
      | some next => exact matchEquivalentPairs_eq_foldlM_zip ps qs next h

/-- `matchEquivalentItemsWithRenaming` is its former body. -/
theorem matchEquivalentItems_old_body (ps qs : List Pattern) (pairs : List (Ident × Ident)) :
    matchEquivalentItemsWithRenaming ps qs pairs
      = if ps.length != qs.length then none
        else (ps.zip qs).foldlM (fun current pq => matchEquivalentWithRenaming pq.1 pq.2 current) pairs := by
  unfold matchEquivalentItemsWithRenaming
  by_cases h : ps.length = qs.length
  · simp [h, matchEquivalentPairs_eq_foldlM_zip ps qs pairs h]
  · simp [h]

/-! ### Table facts -/

theorem binderRenaming?_eq_none_iff (x : Ident) (t : List (Ident × Ident)) :
    binderRenaming? x t = none ↔ x ∉ t.map Prod.fst := by
  induction t with
  | nil => simp [binderRenaming?]
  | cons head tail ih =>
    obtain ⟨l, r⟩ := head
    by_cases hx : l = x
    · subst hx; simp [binderRenaming?]
    · simp [binderRenaming?, hx, ih, Ne.symm hx]

theorem binderRenaming?_mem {x y : Ident} {t : List (Ident × Ident)} (h : binderRenaming? x t = some y) :
    (x, y) ∈ t := by
  induction t with
  | nil => simp [binderRenaming?] at h
  | cons head tail ih =>
    obtain ⟨l, r⟩ := head
    by_cases hx : l = x
    · subst hx; simp [binderRenaming?] at h; simp [h]
    · simp [binderRenaming?, hx] at h; exact List.mem_cons_of_mem _ (ih h)

theorem binderRenaming?_of_mem {x y : Ident} {t : List (Ident × Ident)} (hn : (t.map Prod.fst).Nodup)
    (h : (x, y) ∈ t) : binderRenaming? x t = some y := by
  induction t with
  | nil => simp at h
  | cons head tail ih =>
    obtain ⟨l, r⟩ := head
    simp only [List.map_cons, List.nodup_cons] at hn
    simp only [List.mem_cons, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩ | h
    · simp [binderRenaming?]
    · have hne : l ≠ x := by
        intro hlx; subst hlx; exact hn.1 (List.mem_map.2 ⟨(l, y), h, rfl⟩)
      simp [binderRenaming?, hne, ih hn.2 h]

theorem binderTargetUsed_iff (y : Ident) (t : List (Ident × Ident)) :
    binderTargetUsed y t = true ↔ y ∈ t.map Prod.snd := by
  induction t with
  | nil => simp [binderTargetUsed]
  | cons head tail ih =>
    obtain ⟨l, r⟩ := head
    simp only [binderTargetUsed, Bool.or_eq_true, decide_eq_true_eq, ih, List.map_cons, List.mem_cons]
    exact ⟨fun h => h.elim (fun e => Or.inl e.symm) Or.inr, fun h => h.elim (fun e => Or.inl e.symm) Or.inr⟩

theorem inj_of_nodup_map {α β : Type} (f : α → β) {l : List α} (hn : (l.map f).Nodup) {a b : α}
    (ha : a ∈ l) (hb : b ∈ l) (h : f a = f b) : a = b := by
  induction l with
  | nil => simp at ha
  | cons c rest ih =>
    simp only [List.map_cons, List.nodup_cons] at hn
    simp only [List.mem_cons] at ha hb
    rcases ha with rfl | ha <;> rcases hb with rfl | hb
    · rfl
    · exact absurd (h ▸ List.mem_map.2 ⟨b, hb, rfl⟩) hn.1
    · exact absurd (h.symm ▸ List.mem_map.2 ⟨a, ha, rfl⟩) hn.1
    · exact ih hn.2 ha hb

/-- A WELL-FORMED renaming table: an injective partial map — no left name twice, no right
    name twice. Arbitrary seeds need not be well formed (their behavior is the equations above);
    the empty seed of `isMatchEquivalent` is. -/
def RenamingWF (t : List (Ident × Ident)) : Prop :=
  (t.map Prod.fst).Nodup ∧ (t.map Prod.snd).Nodup

theorem renamingWF_nil : RenamingWF [] := ⟨by simp, by simp⟩

/-- Every entry of `t` is an entry of `m`. -/
def Sub (t m : List (Ident × Ident)) : Prop := ∀ e ∈ t, e ∈ m

mutual
  /-- Rename every binder of a pattern through a table (a binder without an entry keeps its
      name); literals, kinds, lengths and nesting are untouched. -/
  def renameWith (t : List (Ident × Ident)) : Pattern → Pattern
    | .bind x => .bind ((binderRenaming? x t).getD x)
    | .litInt n => .litInt n
    | .litString s => .litString s
    | .litBool b => .litBool b
    | .sequenceValue ps => .sequenceValue (renameAllWith t ps)
    | .listValue ps => .listValue (renameAllWith t ps)

  def renameAllWith (t : List (Ident × Ident)) : List Pattern → List Pattern
    | [] => []
    | p :: ps => renameWith t p :: renameAllWith t ps
end

mutual
  /-- The table has an entry for every binder of the pattern. -/
  def Covers (t : List (Ident × Ident)) : Pattern → Prop
    | .bind x => (binderRenaming? x t).isSome = true
    | .litInt _ => True
    | .litString _ => True
    | .litBool _ => True
    | .sequenceValue ps => CoversAll t ps
    | .listValue ps => CoversAll t ps

  def CoversAll (t : List (Ident × Ident)) : List Pattern → Prop
    | [] => True
    | p :: ps => Covers t p ∧ CoversAll t ps
end

theorem renameAllWith_length (t : List (Ident × Ident)) : (ps : List Pattern) →
    (renameAllWith t ps).length = ps.length
  | [] => rfl
  | _ :: ps => by simp [renameAllWith, renameAllWith_length t ps]

/-! ### Extension: what a success adds -/

/-- What a successful comparison does to the table: it PREPENDS pairs for left names it did
    not know, in traversal order, keeping the seed as a suffix. -/
def Extends (t out : List (Ident × Ident)) : Prop :=
  ∃ added, out = added ++ t ∧ ∀ l ∈ added.map Prod.fst, binderRenaming? l t = none

theorem extends_refl (t : List (Ident × Ident)) : Extends t t := ⟨[], by simp, by simp⟩

theorem binderRenaming?_append_none (x : Ident) (a t : List (Ident × Ident))
    (h : binderRenaming? x (a ++ t) = none) : binderRenaming? x t = none := by
  rw [binderRenaming?_eq_none_iff] at h ⊢
  simp only [List.map_append, List.mem_append, not_or] at h
  exact h.2

theorem extends_trans {a b c : List (Ident × Ident)} (h1 : Extends a b) (h2 : Extends b c) : Extends a c := by
  obtain ⟨d1, rfl, f1⟩ := h1
  obtain ⟨d2, rfl, f2⟩ := h2
  refine ⟨d2 ++ d1, by simp, ?_⟩
  intro l hl
  simp only [List.map_append, List.mem_append] at hl
  rcases hl with hl | hl
  · exact binderRenaming?_append_none l d1 a (f2 l hl)
  · exact f1 l hl

mutual
  theorem equiv_extends : (p q : Pattern) → (t out : List (Ident × Ident)) →
      matchEquivalentWithRenaming p q t = some out → Extends t out
    | .bind l, q, t, out, h => by
        cases q <;> simp only [matchEquivalentWithRenaming, reduceCtorEq] at h
        rename_i r
        cases hl : binderRenaming? l t with
        | some e =>
            simp only [hl] at h
            split at h
            · cases h; exact extends_refl t
            · cases h
        | none =>
            simp only [hl] at h
            split at h
            · cases h
            · cases h; exact ⟨[(l, r)], rfl, by simpa using hl⟩
    | .litInt _, q, t, out, h => by
        cases q <;> simp only [matchEquivalentWithRenaming, reduceCtorEq] at h
        split at h
        · cases h; exact extends_refl t
        · cases h
    | .litString _, q, t, out, h => by
        cases q <;> simp only [matchEquivalentWithRenaming, reduceCtorEq] at h
        split at h
        · cases h; exact extends_refl t
        · cases h
    | .litBool _, q, t, out, h => by
        cases q <;> simp only [matchEquivalentWithRenaming, reduceCtorEq] at h
        split at h
        · cases h; exact extends_refl t
        · cases h
    | .sequenceValue ps, q, t, out, h => by
        cases q <;> simp only [matchEquivalentWithRenaming, reduceCtorEq] at h
        rename_i qs
        split at h
        · cases h
        · exact equivPairs_extends ps qs t out h
    | .listValue ps, q, t, out, h => by
        cases q <;> simp only [matchEquivalentWithRenaming, reduceCtorEq] at h
        rename_i qs
        split at h
        · cases h
        · exact equivPairs_extends ps qs t out h

  theorem equivPairs_extends : (ps qs : List Pattern) → (t out : List (Ident × Ident)) →
      matchEquivalentPairsWithRenaming ps qs t = some out → Extends t out
    | [], [], t, out, h => by
        simp only [matchEquivalentPairsWithRenaming, Option.some.injEq] at h
        subst h; exact extends_refl t
    | [], _ :: _, _, _, h => by simp [matchEquivalentPairsWithRenaming] at h
    | _ :: _, [], _, _, h => by simp [matchEquivalentPairsWithRenaming] at h
    | p :: ps, q :: qs, t, out, h => by
        simp only [matchEquivalentPairsWithRenaming, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
        obtain ⟨next, h1, h2⟩ := h
        exact extends_trans (equiv_extends p q t next h1) (equivPairs_extends ps qs next out h2)
end

theorem sub_of_extends {t out : List (Ident × Ident)} (h : Extends t out) : Sub t out := by
  obtain ⟨added, rfl, _⟩ := h
  intro e he; exact List.mem_append_right _ he

/-! ### Well-formedness is preserved -/

mutual
  /-- A success from a well-formed table returns a well-formed (injective) table. -/
  theorem equiv_wf : (p q : Pattern) → (t out : List (Ident × Ident)) → RenamingWF t →
      matchEquivalentWithRenaming p q t = some out → RenamingWF out
    | .bind l, q, t, out, hwf, h => by
        cases q <;> simp only [matchEquivalentWithRenaming, reduceCtorEq] at h
        rename_i r
        cases hl : binderRenaming? l t with
        | some e =>
            simp only [hl] at h
            split at h
            · cases h; exact hwf
            · cases h
        | none =>
            simp only [hl] at h
            split at h
            · cases h
            · rename_i hu
              cases h
              refine ⟨?_, ?_⟩
              · simp only [List.map_cons, List.nodup_cons]
                exact ⟨(binderRenaming?_eq_none_iff l t).1 hl, hwf.1⟩
              · simp only [List.map_cons, List.nodup_cons]
                refine ⟨?_, hwf.2⟩
                intro hm
                exact hu ((binderTargetUsed_iff r t).2 hm)
    | .litInt _, q, t, out, hwf, h => by
        cases q <;> simp only [matchEquivalentWithRenaming, reduceCtorEq] at h
        split at h
        · cases h; exact hwf
        · cases h
    | .litString _, q, t, out, hwf, h => by
        cases q <;> simp only [matchEquivalentWithRenaming, reduceCtorEq] at h
        split at h
        · cases h; exact hwf
        · cases h
    | .litBool _, q, t, out, hwf, h => by
        cases q <;> simp only [matchEquivalentWithRenaming, reduceCtorEq] at h
        split at h
        · cases h; exact hwf
        · cases h
    | .sequenceValue ps, q, t, out, hwf, h => by
        cases q <;> simp only [matchEquivalentWithRenaming, reduceCtorEq] at h
        rename_i qs
        split at h
        · cases h
        · exact equivPairs_wf ps qs t out hwf h
    | .listValue ps, q, t, out, hwf, h => by
        cases q <;> simp only [matchEquivalentWithRenaming, reduceCtorEq] at h
        rename_i qs
        split at h
        · cases h
        · exact equivPairs_wf ps qs t out hwf h

  theorem equivPairs_wf : (ps qs : List Pattern) → (t out : List (Ident × Ident)) → RenamingWF t →
      matchEquivalentPairsWithRenaming ps qs t = some out → RenamingWF out
    | [], [], t, out, hwf, h => by
        simp only [matchEquivalentPairsWithRenaming, Option.some.injEq] at h
        subst h; exact hwf
    | [], _ :: _, _, _, _, h => by simp [matchEquivalentPairsWithRenaming] at h
    | _ :: _, [], _, _, _, h => by simp [matchEquivalentPairsWithRenaming] at h
    | p :: ps, q :: qs, t, out, hwf, h => by
        simp only [matchEquivalentPairsWithRenaming, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
        obtain ⟨next, h1, h2⟩ := h
        exact equivPairs_wf ps qs next out (equiv_wf p q t next hwf h1) h2
end

/-! ### Soundness and completeness: structural equality up to injective renaming -/

theorem lookup_of_sub {m t : List (Ident × Ident)} (hwf : RenamingWF m) (hs : Sub t m) {x y : Ident}
    (h : (x, y) ∈ t) : binderRenaming? x m = some y :=
  binderRenaming?_of_mem hwf.1 (hs _ h)

mutual
  /-- SOUNDNESS: a success means the right pattern is the left one renamed through ANY
      well-formed table containing the returned one — in particular the returned table itself
      — which covers every left binder. -/
  theorem equiv_sound : (p q : Pattern) → (t out : List (Ident × Ident)) →
      matchEquivalentWithRenaming p q t = some out →
      ∀ m, RenamingWF m → Sub out m → renameWith m p = q ∧ Covers m p
    | .bind l, q, t, out, h, m, hwf, hs => by
        cases q <;> simp only [matchEquivalentWithRenaming, reduceCtorEq] at h
        rename_i r
        have key : binderRenaming? l m = some r := by
          cases hl : binderRenaming? l t with
          | some e =>
              simp only [hl] at h
              split at h
              · rename_i he; cases h; subst he
                exact lookup_of_sub hwf hs (binderRenaming?_mem hl)
              · cases h
          | none =>
              simp only [hl] at h
              split at h
              · cases h
              · cases h; exact lookup_of_sub hwf hs (List.mem_cons_self ..)
        simp [renameWith, Covers, key]
    | .litInt _, q, t, out, h, m, _, _ => by
        cases q <;> simp only [matchEquivalentWithRenaming, reduceCtorEq] at h
        split at h
        · rename_i he; subst he; simp [renameWith, Covers]
        · cases h
    | .litString _, q, t, out, h, m, _, _ => by
        cases q <;> simp only [matchEquivalentWithRenaming, reduceCtorEq] at h
        split at h
        · rename_i he; subst he; simp [renameWith, Covers]
        · cases h
    | .litBool _, q, t, out, h, m, _, _ => by
        cases q <;> simp only [matchEquivalentWithRenaming, reduceCtorEq] at h
        split at h
        · rename_i he; subst he; simp [renameWith, Covers]
        · cases h
    | .sequenceValue ps, q, t, out, h, m, hwf, hs => by
        cases q <;> simp only [matchEquivalentWithRenaming, reduceCtorEq] at h
        rename_i qs
        split at h
        · cases h
        · have := equivPairs_sound ps qs t out h m hwf hs
          simp [renameWith, Covers, this.1, this.2]
    | .listValue ps, q, t, out, h, m, hwf, hs => by
        cases q <;> simp only [matchEquivalentWithRenaming, reduceCtorEq] at h
        rename_i qs
        split at h
        · cases h
        · have := equivPairs_sound ps qs t out h m hwf hs
          simp [renameWith, Covers, this.1, this.2]

  theorem equivPairs_sound : (ps qs : List Pattern) → (t out : List (Ident × Ident)) →
      matchEquivalentPairsWithRenaming ps qs t = some out →
      ∀ m, RenamingWF m → Sub out m → renameAllWith m ps = qs ∧ CoversAll m ps
    | [], [], _, _, _, _, _, _ => by simp [renameAllWith, CoversAll]
    | [], _ :: _, _, _, h, _, _, _ => by simp [matchEquivalentPairsWithRenaming] at h
    | _ :: _, [], _, _, h, _, _, _ => by simp [matchEquivalentPairsWithRenaming] at h
    | p :: ps, q :: qs, t, out, h, m, hwf, hs => by
        simp only [matchEquivalentPairsWithRenaming, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
        obtain ⟨next, h1, h2⟩ := h
        have hrest := equivPairs_sound ps qs next out h2 m hwf hs
        have hnext : Sub next m := fun e he => hs e (sub_of_extends (equivPairs_extends ps qs next out h2) e he)
        have hhead := equiv_sound p q t next h1 m hwf hnext
        simp [renameAllWith, CoversAll, hhead.1, hhead.2, hrest.1, hrest.2]
end

mutual
  /-- COMPLETENESS: renaming a pattern through a well-formed table covering its binders gives
      an equivalent pattern, from every seed contained in that table. -/
  theorem equiv_complete : (p : Pattern) → (t m : List (Ident × Ident)) → RenamingWF m →
      Covers m p → Sub t m →
      ∃ out, matchEquivalentWithRenaming p (renameWith m p) t = some out ∧ Sub out m
    | .bind l, t, m, hwf, hc, hs => by
        simp only [Covers, Option.isSome_iff_exists] at hc
        obtain ⟨r, hr⟩ := hc
        simp only [renameWith, hr, Option.getD_some]
        cases hl : binderRenaming? l t with
        | some e =>
            have he : e = r := by
              have := lookup_of_sub hwf hs (binderRenaming?_mem hl)
              rw [hr] at this; exact (Option.some.inj this).symm
            subst he
            exact ⟨t, by simp [matchEquivalentWithRenaming, hl], hs⟩
        | none =>
            have hu : binderTargetUsed r t = false := by
              cases hb : binderTargetUsed r t with
              | false => rfl
              | true =>
                  obtain ⟨⟨a, b⟩, hab, hb'⟩ := List.mem_map.1 ((binderTargetUsed_iff r t).1 hb)
                  simp only at hb'; subst hb'
                  have ha : (a, b) = (l, b) :=
                    inj_of_nodup_map Prod.snd hwf.2 (hs _ hab) (binderRenaming?_mem hr) rfl
                  have ha2 : a = l := congrArg Prod.fst ha
                  subst ha2
                  exact absurd (List.mem_map.2 ⟨(a, b), hab, rfl⟩) ((binderRenaming?_eq_none_iff a t).1 hl)
            refine ⟨(l, r) :: t, by simp [matchEquivalentWithRenaming, hl, hu], ?_⟩
            intro e he
            simp only [List.mem_cons] at he
            rcases he with rfl | he
            · exact binderRenaming?_mem hr
            · exact hs e he
    | .litInt n, t, m, _, _, hs => ⟨t, by simp [renameWith, matchEquivalentWithRenaming], hs⟩
    | .litString s, t, m, _, _, hs => ⟨t, by simp [renameWith, matchEquivalentWithRenaming], hs⟩
    | .litBool b, t, m, _, _, hs => ⟨t, by simp [renameWith, matchEquivalentWithRenaming], hs⟩
    | .sequenceValue ps, t, m, hwf, hc, hs => by
        simp only [Covers] at hc
        obtain ⟨out, h, hout⟩ := equivPairs_complete ps t m hwf hc hs
        exact ⟨out, by simp [renameWith, matchEquivalentWithRenaming, renameAllWith_length, h], hout⟩
    | .listValue ps, t, m, hwf, hc, hs => by
        simp only [Covers] at hc
        obtain ⟨out, h, hout⟩ := equivPairs_complete ps t m hwf hc hs
        exact ⟨out, by simp [renameWith, matchEquivalentWithRenaming, renameAllWith_length, h], hout⟩

  theorem equivPairs_complete : (ps : List Pattern) → (t m : List (Ident × Ident)) → RenamingWF m →
      CoversAll m ps → Sub t m →
      ∃ out, matchEquivalentPairsWithRenaming ps (renameAllWith m ps) t = some out ∧ Sub out m
    | [], t, _, _, _, hs => ⟨t, by simp [renameAllWith, matchEquivalentPairsWithRenaming], hs⟩
    | p :: ps, t, m, hwf, hc, hs => by
        simp only [CoversAll] at hc
        obtain ⟨next, h1, hnext⟩ := equiv_complete p t m hwf hc.1 hs
        obtain ⟨out, h2, hout⟩ := equivPairs_complete ps next m hwf hc.2 hnext
        exact ⟨out, by simp [renameAllWith, matchEquivalentPairsWithRenaming, h1, h2], hout⟩
end

/-- THE STRUCTURAL CHARACTERIZATION of the duplicate-clause relation: two patterns are
    match-equivalent exactly when the right one is the left one with its binders renamed through
    an INJECTIVE table defined on all of them. Literal payloads, constructor kinds, lengths and
    nesting are therefore equal, and two binder positions carry the same name on the left iff
    they do on the right — across nested siblings too. -/
theorem isMatchEquivalent_iff (p q : Pattern) :
    p.isMatchEquivalent q = true ↔ ∃ m, RenamingWF m ∧ Covers m p ∧ renameWith m p = q := by
  constructor
  · intro h
    simp only [isMatchEquivalent, Option.isSome_iff_exists] at h
    obtain ⟨out, h⟩ := h
    have hwf := equiv_wf p q [] out renamingWF_nil h
    have hs := equiv_sound p q [] out h out hwf (fun _ he => he)
    exact ⟨out, hwf, hs.2, hs.1⟩
  · rintro ⟨m, hwf, hc, rfl⟩
    obtain ⟨out, h, _⟩ := equiv_complete p [] m hwf hc (fun _ he => by simp at he)
    simp [isMatchEquivalent, h]

/-- The table a closed comparison returns is itself the injective witness. -/
theorem isMatchEquivalent_witness {p q : Pattern} {out : List (Ident × Ident)}
    (h : matchEquivalentWithRenaming p q [] = some out) :
    RenamingWF out ∧ Covers out p ∧ renameWith out p = q := by
  have hwf := equiv_wf p q [] out renamingWF_nil h
  have hs := equiv_sound p q [] out h out hwf (fun _ he => he)
  exact ⟨hwf, hs.2, hs.1⟩

/-! ### Reflexivity and symmetry -/

/-- A table that renames every name to itself. -/
def IdTable (t : List (Ident × Ident)) : Prop := ∀ e ∈ t, e.1 = e.2

mutual
  theorem equiv_refl_aux : (p : Pattern) → (t : List (Ident × Ident)) → IdTable t →
      ∃ out, matchEquivalentWithRenaming p p t = some out ∧ IdTable out
    | .bind x, t, ht => by
        cases hl : binderRenaming? x t with
        | some e =>
            have he : x = e := ht _ (binderRenaming?_mem hl)
            subst he
            exact ⟨t, by simp [matchEquivalentWithRenaming, hl], ht⟩
        | none =>
            have hu : binderTargetUsed x t = false := by
              cases hb : binderTargetUsed x t with
              | false => rfl
              | true =>
                  obtain ⟨⟨a, b⟩, hab, hb'⟩ := List.mem_map.1 ((binderTargetUsed_iff x t).1 hb)
                  simp only at hb'; subst hb'
                  have ha : a = b := ht _ hab
                  subst ha
                  exact absurd (List.mem_map.2 ⟨(a, a), hab, rfl⟩) ((binderRenaming?_eq_none_iff a t).1 hl)
            refine ⟨(x, x) :: t, by simp [matchEquivalentWithRenaming, hl, hu], ?_⟩
            intro e he
            simp only [List.mem_cons] at he
            rcases he with rfl | he
            · rfl
            · exact ht e he
    | .litInt _, t, ht => ⟨t, by simp [matchEquivalentWithRenaming], ht⟩
    | .litString _, t, ht => ⟨t, by simp [matchEquivalentWithRenaming], ht⟩
    | .litBool _, t, ht => ⟨t, by simp [matchEquivalentWithRenaming], ht⟩
    | .sequenceValue ps, t, ht => by
        obtain ⟨out, h, hout⟩ := equivPairs_refl_aux ps t ht
        exact ⟨out, by simp [matchEquivalentWithRenaming, h], hout⟩
    | .listValue ps, t, ht => by
        obtain ⟨out, h, hout⟩ := equivPairs_refl_aux ps t ht
        exact ⟨out, by simp [matchEquivalentWithRenaming, h], hout⟩

  theorem equivPairs_refl_aux : (ps : List Pattern) → (t : List (Ident × Ident)) → IdTable t →
      ∃ out, matchEquivalentPairsWithRenaming ps ps t = some out ∧ IdTable out
    | [], t, ht => ⟨t, by simp [matchEquivalentPairsWithRenaming], ht⟩
    | p :: ps, t, ht => by
        obtain ⟨next, h1, hn⟩ := equiv_refl_aux p t ht
        obtain ⟨out, h2, hout⟩ := equivPairs_refl_aux ps next hn
        exact ⟨out, by simp [matchEquivalentPairsWithRenaming, h1, h2], hout⟩
end

/-- Every pattern is a duplicate of itself (so two clauses with one head are duplicates,
    whatever their bodies). -/
theorem isMatchEquivalent_refl (p : Pattern) : p.isMatchEquivalent p = true := by
  obtain ⟨out, h, _⟩ := equiv_refl_aux p [] (fun _ he => by simp at he)
  simp [isMatchEquivalent, h]

/-- The inverse table. -/
def swapTable (m : List (Ident × Ident)) : List (Ident × Ident) := m.map Prod.swap

theorem swapTable_wf {m : List (Ident × Ident)} (h : RenamingWF m) : RenamingWF (swapTable m) := by
  simp only [RenamingWF, swapTable, List.map_map]
  exact ⟨by simpa [Function.comp_def] using h.2, by simpa [Function.comp_def] using h.1⟩

mutual
  /-- Renaming back through the inverse table restores the pattern. -/
  theorem rename_swap : (p : Pattern) → (m : List (Ident × Ident)) → RenamingWF m → Covers m p →
      Covers (swapTable m) (renameWith m p) ∧ renameWith (swapTable m) (renameWith m p) = p
    | .bind x, m, hwf, hc => by
        simp only [Covers, Option.isSome_iff_exists] at hc
        obtain ⟨y, hy⟩ := hc
        have hmem : (y, x) ∈ swapTable m := List.mem_map.2 ⟨(x, y), binderRenaming?_mem hy, rfl⟩
        have hback : binderRenaming? y (swapTable m) = some x :=
          binderRenaming?_of_mem (swapTable_wf hwf).1 hmem
        simp [renameWith, Covers, hy, hback]
    | .litInt _, _, _, _ => by simp [renameWith, Covers]
    | .litString _, _, _, _ => by simp [renameWith, Covers]
    | .litBool _, _, _, _ => by simp [renameWith, Covers]
    | .sequenceValue ps, m, hwf, hc => by
        simp only [Covers] at hc
        have := rename_swap_all ps m hwf hc
        simp [renameWith, Covers, this.1, this.2]
    | .listValue ps, m, hwf, hc => by
        simp only [Covers] at hc
        have := rename_swap_all ps m hwf hc
        simp [renameWith, Covers, this.1, this.2]

  theorem rename_swap_all : (ps : List Pattern) → (m : List (Ident × Ident)) → RenamingWF m →
      CoversAll m ps →
      CoversAll (swapTable m) (renameAllWith m ps) ∧ renameAllWith (swapTable m) (renameAllWith m ps) = ps
    | [], _, _, _ => by simp [renameAllWith, CoversAll]
    | p :: ps, m, hwf, hc => by
        simp only [CoversAll] at hc
        have h1 := rename_swap p m hwf hc.1
        have h2 := rename_swap_all ps m hwf hc.2
        simp [renameAllWith, CoversAll, h1.1, h1.2, h2.1, h2.2]
end

/-- The duplicate relation is symmetric. -/
theorem isMatchEquivalent_symm (p q : Pattern) : p.isMatchEquivalent q = q.isMatchEquivalent p := by
  have dir : ∀ a b : Pattern, a.isMatchEquivalent b = true → b.isMatchEquivalent a = true := by
    intro a b h
    obtain ⟨m, hwf, hc, rfl⟩ := (isMatchEquivalent_iff a b).1 h
    have := rename_swap a m hwf hc
    exact (isMatchEquivalent_iff _ _).2 ⟨swapTable m, swapTable_wf hwf, this.1, this.2⟩
  cases h : p.isMatchEquivalent q <;> cases h' : q.isMatchEquivalent p
  · rfl
  · exact absurd (dir q p h') (by simp [h])
  · exact absurd (dir p q h) (by simp [h'])
  · rfl

/-! ### The duplicate-clause check -/

theorem hasDuplicate_go_nil : Algorithm.hasDuplicateBranchPatterns.go [] = false := rfl

theorem hasDuplicate_go_cons (b : CondBranch) (rest : List CondBranch) :
    Algorithm.hasDuplicateBranchPatterns.go (b :: rest)
      = (rest.any (fun br => b.pattern.isMatchEquivalent br.pattern)
          || Algorithm.hasDuplicateBranchPatterns.go rest) := by
  simp only [Algorithm.hasDuplicateBranchPatterns.go]
  split <;> simp_all

theorem hasDuplicateBranchPatterns_conditional (parent : Option ScopeCtx) (opens : List Expr)
    (bs : List CondBranch) (id : Option PropertyIdentity) :
    (Algorithm.conditional parent opens bs id).hasDuplicateBranchPatterns
      = Algorithm.hasDuplicateBranchPatterns.go bs := rfl

/-- The check passes EXACTLY when no clause is match-equivalent to a LATER clause. -/
theorem hasDuplicate_go_false_iff (bs : List CondBranch) :
    Algorithm.hasDuplicateBranchPatterns.go bs = false
      ↔ bs.Pairwise (fun b b' => b.pattern.isMatchEquivalent b'.pattern = false) := by
  induction bs with
  | nil => simp [hasDuplicate_go_nil]
  | cons b rest ih =>
    rw [hasDuplicate_go_cons, List.pairwise_cons, ← ih]
    simp [List.any_eq_false]

/-- The check reads the clause PATTERNS only: clause bodies never decide it. -/
theorem hasDuplicate_go_patterns_only : (bs bs' : List CondBranch) →
    bs.map CondBranch.pattern = bs'.map CondBranch.pattern →
    Algorithm.hasDuplicateBranchPatterns.go bs = Algorithm.hasDuplicateBranchPatterns.go bs'
  | [], [], _ => rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | b :: rest, b' :: rest', h => by
      simp only [List.map_cons, List.cons.injEq] at h
      rw [hasDuplicate_go_cons, hasDuplicate_go_cons, hasDuplicate_go_patterns_only rest rest' h.2, h.1]
      congr 1
      have hm : ∀ (l l' : List CondBranch), l.map CondBranch.pattern = l'.map CondBranch.pattern →
          ∀ (f : Pattern → Bool), l.any (fun br => f br.pattern) = l'.any (fun br => f br.pattern) := by
        intro l l' hl f
        induction l generalizing l' with
        | nil => cases l' <;> simp_all
        | cons x xs ihx => cases l' with
          | nil => simp at hl
          | cons y ys =>
              simp only [List.map_cons, List.cons.injEq] at hl
              simp [hl.1, ihx ys hl.2]
      exact hm rest rest' h.2 (fun q => b'.pattern.isMatchEquivalent q)

/-- A clause whose head is an earlier clause's head under an injective renaming of all its
    binders makes the family a duplicate family. -/
theorem renamed_clause_is_a_duplicate (pre mid post : List CondBranch) (b b' : CondBranch)
    (m : List (Ident × Ident)) (hwf : RenamingWF m) (hc : Covers m b.pattern)
    (hr : renameWith m b.pattern = b'.pattern) :
    Algorithm.hasDuplicateBranchPatterns.go (pre ++ b :: (mid ++ b' :: post)) = true := by
  have heq : b.pattern.isMatchEquivalent b'.pattern = true :=
    (isMatchEquivalent_iff _ _).2 ⟨m, hwf, hc, hr⟩
  cases h : Algorithm.hasDuplicateBranchPatterns.go (pre ++ b :: (mid ++ b' :: post)) with
  | true => rfl
  | false =>
      have hp := (hasDuplicate_go_false_iff _).1 h
      rw [List.pairwise_append, List.pairwise_cons] at hp
      have := hp.2.1.1 b' (by simp)
      rw [heq] at this; cases this

/-- Conversely, a family none of whose clause heads is a renaming of a later one passes. -/
theorem unrenamed_family_passes (bs : List CondBranch)
    (h : bs.Pairwise (fun b b' => ¬ ∃ m, RenamingWF m ∧ Covers m b.pattern ∧ renameWith m b.pattern = b'.pattern)) :
    Algorithm.hasDuplicateBranchPatterns.go bs = false := by
  rw [hasDuplicate_go_false_iff]
  refine h.imp ?_
  intro b b' hn
  cases he : b.pattern.isMatchEquivalent b'.pattern with
  | false => rfl
  | true => exact absurd ((isMatchEquivalent_iff _ _).1 he) hn

end Renaming

/-! ## Production: the binder's and the dispatcher's decisions through the total helpers -/

section Production

variable (k : NeedCapabilities EvalM) (address : Nat) (repeated : List Ident) (bound : NeedEnv)
  (family : Bool) (s t : EvalState) (value : Result) (count : Nat)

/-- THE LITERAL ARM, decided: after its cell's VALUE demand returned `value`, a literal pattern
    matches iff `value` is that literal's own constructor with that payload. -/
theorem bindOne_literal_decided (literal : Pattern)
    (hv : runEval (k.value address) s = (.ok (value, count), t)) :
    runEval (NeedBinder.bindOne k (.literal literal) address repeated bound family) s
      = (.ok (if (matchPattern literal value).isSome then some bound else none), t) := by
  simp [NeedBinder.bindOne, hv]

theorem bindOne_litInt (n : Int) (hv : runEval (k.value address) s = (.ok (value, count), t)) :
    runEval (NeedBinder.bindOne k (.literal (.litInt n)) address repeated bound family) s
      = (.ok (if value == .atom n then some bound else none), t) := by
  rw [bindOne_literal_decided k address repeated bound family s t value count _ hv]
  simp only [matchPattern, matchPatternInto_litInt]
  split <;> simp_all

theorem bindOne_litString (str : String) (hv : runEval (k.value address) s = (.ok (value, count), t)) :
    runEval (NeedBinder.bindOne k (.literal (.litString str)) address repeated bound family) s
      = (.ok (if value == .str str then some bound else none), t) := by
  rw [bindOne_literal_decided k address repeated bound family s t value count _ hv]
  simp only [matchPattern, matchPatternInto_litString]
  split <;> simp_all

theorem bindOne_litBool (b : Bool) (hv : runEval (k.value address) s = (.ok (value, count), t)) :
    runEval (NeedBinder.bindOne k (.literal (.litBool b)) address repeated bound family) s
      = (.ok (if value == .bool b then some bound else none), t) := by
  rw [bindOne_literal_decided k address repeated bound family s t value count _ hv]
  simp only [matchPattern, matchPatternInto_litBool]
  split <;> simp_all

/-- The literal of a clause head IS one of the three literal constructors. -/
theorem ofClause_literal (p literal : Pattern) (h : NeedPattern.ofClause p = .literal literal) :
    literal = p ∧ ((∃ n, p = .litInt n) ∨ (∃ str, p = .litString str) ∨ (∃ b, p = .litBool b)) := by
  cases p <;> simp [NeedPattern.ofClause] at h ⊢ <;> first | (subst h; simp) | skip

/-- THE KIND-MISMATCH ERROR of an ordinary sequence pattern, as an explicit string: the written
    pattern, then the received value described by `operandDescription`. -/
theorem bindOne_sequence_kind_mismatch (ps : List NeedPattern)
    (hv : runEval (k.value address) s = (.ok (value, count), t))
    (hk : Result.sequencePatternItems? value = none) :
    runEval (NeedBinder.bindOne k (.sequence ps) address repeated bound false) s
      = (.error (Error.typeMismatch ("sequence pattern `"
          ++ (ParameterPattern.sequenceValue (ps.map NeedPattern.toParameter)).displayName
          ++ "` expects a sequence value, but received " ++ operandDescription value)), t) := by
  simp [NeedBinder.bindOne, hv, hk]
  simp only [NeedPattern.toParameter]; rfl

theorem bindOne_list_kind_mismatch (ps : List NeedPattern)
    (hv : runEval (k.value address) s = (.ok (value, count), t))
    (hk : Result.listPatternItems? value = none) :
    runEval (NeedBinder.bindOne k (.list ps) address repeated bound false) s
      = (.error (Error.typeMismatch ("list pattern `"
          ++ (ParameterPattern.listValue (ps.map NeedPattern.toParameter)).displayName
          ++ "` expects a list value, but received " ++ operandDescription value)), t) := by
  simp [NeedBinder.bindOne, hv, hk]
  simp only [NeedPattern.toParameter]; rfl

/-- In a clause family the same mismatch only rejects the clause. -/
theorem bindOne_sequence_kind_mismatch_family (ps : List NeedPattern)
    (hv : runEval (k.value address) s = (.ok (value, count), t))
    (hk : Result.sequencePatternItems? value = none) :
    runEval (NeedBinder.bindOne k (.sequence ps) address repeated bound true) s = (.ok none, t) := by
  simp [NeedBinder.bindOne, hv, hk]

theorem bindOne_list_kind_mismatch_family (ps : List NeedPattern)
    (hv : runEval (k.value address) s = (.ok (value, count), t))
    (hk : Result.listPatternItems? value = none) :
    runEval (NeedBinder.bindOne k (.list ps) address repeated bound true) s = (.ok none, t) := by
  simp [NeedBinder.bindOne, hv, hk]

end Production

/-- The production binder's literal arm (`bindNeedOne`, the core at `c.capabilities`), for an
    integer literal of a clause head. -/
theorem production_literal_int (c : NeedChannels) (n : Int) (address : Nat) (repeated : List Ident)
    (bound : NeedEnv) (family : Bool) (s t : EvalState) (value : Result) (count : Nat)
    (hv : runEval (c.capabilities.value address) s = (.ok (value, count), t)) :
    (bindNeedOne c (NeedPattern.ofClause (.litInt n)) address repeated bound family).runState s
      = (.ok (if value == .atom n then some bound else none), t) := by
  rw [BinderCore.production_one_is_the_core, show NeedPattern.ofClause (.litInt n) = .literal (.litInt n) by simp [NeedPattern.ofClause]]
  exact bindOne_litInt c.capabilities address repeated bound family s t value count n hv

/-- The production binder's kind-mismatch error for an ordinary sequence pattern. -/
theorem production_sequence_kind_mismatch (c : NeedChannels) (ps : List NeedPattern) (address : Nat)
    (repeated : List Ident) (bound : NeedEnv) (s t : EvalState) (value : Result) (count : Nat)
    (hv : runEval (c.capabilities.value address) s = (.ok (value, count), t))
    (hk : Result.sequencePatternItems? value = none) :
    (bindNeedOne c (.sequence ps) address repeated bound false).runState s
      = (.error (Error.typeMismatch ("sequence pattern `"
          ++ (ParameterPattern.sequenceValue (ps.map NeedPattern.toParameter)).displayName
          ++ "` expects a sequence value, but received " ++ operandDescription value)), t) := by
  rw [BinderCore.production_one_is_the_core]
  exact bindOne_sequence_kind_mismatch c.capabilities address repeated bound s t value count ps hv hk

/-- THE PRODUCTION DISPATCHER rejects a family containing a renamed duplicate head before the
    count check, before any attempt and with the state unchanged — whatever the clause bodies,
    the supplied cells, the context and the channels. -/
theorem production_dispatch_rejects_a_renamed_duplicate (c : NeedChannels) (parent : Option ScopeCtx)
    (opens : List Expr) (pre mid post : List CondBranch) (b b' : CondBranch)
    (id : Option PropertyIdentity) (m : List (Ident × Ident)) (hwf : RenamingWF m)
    (hc : Covers m b.pattern) (hr : renameWith m b.pattern = b'.pattern)
    (cells : List Nat) (ctx : EvalCtx) (env : ValEnv) (name : String) (s : EvalState) :
    (selectNeedFamilyBranch c (.conditional parent opens (pre ++ b :: (mid ++ b' :: post)) id)
        cells ctx env name).runState s
      = (.error Error.duplicateBranchPattern, s) := by
  rw [BinderCore.production_dispatcher_is_the_core]
  exact FamilyDispatch.select_duplicate_first c.capabilities cells name _ _ s
    (renamed_clause_is_a_duplicate pre mid post b b' m hwf hc hr)

/-- A family that passes the duplicate check (no clause is a renaming of a later one) reaches
    the count check and the clause search exactly as `FamilyDispatch.select_count_before_attempts`
    / `select_is_the_search` state. -/
theorem unrenamed_family_has_no_duplicate (parent : Option ScopeCtx) (opens : List Expr)
    (bs : List CondBranch) (id : Option PropertyIdentity)
    (h : bs.Pairwise (fun b b' => ¬ ∃ m, RenamingWF m ∧ Covers m b.pattern ∧ renameWith m b.pattern = b'.pattern)) :
    (Algorithm.conditional parent opens bs id).hasDuplicateBranchPatterns = false :=
  unrenamed_family_passes bs h

end KatLang.PatternHelpers
