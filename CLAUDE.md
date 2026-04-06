# Claude Instructions for KatLang (Lean Spec + C# Toolchain)

This repository contains:

- **`KatLang.lean`** (repository root): the authoritative specification of KatLang’s core syntax, semantics, and invariants.
- A **C# implementation** of KatLang exact syntax, including AST and parser (with evaluator/typechecker as future extensions).

Claude must treat the Lean file as the single source of truth for KatLang’s language design.

Correctness and fidelity to the Lean specification take precedence over convenience, performance, or stylistic preferences.

---

## Architectural Overview

KatLang defines `.dotCall` as a first-class constructor in the Lean core model:

    dotCall : Expr → Ident → Option Algorithm → Expr

This means:

- Dot syntax (`a.f` and `a.f(args)`) is part of the Lean core — not surface sugar.
- Its semantics are defined in Lean (`resolveAlg`, `evalDotCall`).
- C# must faithfully implement this behavior without reinterpretation.

### dotCall Semantics (Normative)

When evaluating:

    a.f
    a.f(args)

Lean enforces:

1. Resolve `a` to an Algorithm.
2. If `f` is a structural property of `a`:
   - If no args and property has 0 parameters → evaluate directly.
   - Otherwise → call with receiver injected as first argument.
3. If `f` is not a structural property → perform lexical lookup (including imports).
4. If multiple imports provide `f` → raise `ambiguousImport`.
5. Fallback occurs only when structural property is absent — not on evaluation failure.

C# must reproduce this logic exactly.

---

## Core Objectives

1. **Spec alignment**
   Ensure the C# implementation exactly matches Lean.

2. **Spec-first evolution**
   New features must be proposed in Lean first.

3. **Long-term maintainability**
   Preserve modular architecture: parser → AST → evaluator → typechecker.

---

## Non-Negotiable Rules

- Do not modify `KatLang.lean` unless explicitly instructed.
- **Bug-fix exception**: When a bug is identified in both the Lean spec and the C# implementation, fix both simultaneously. The Lean model is the source of truth, so a bug in Lean must be corrected there first (or together with C#) to keep the spec accurate.
- Do not invent syntax or semantics.
- If intuition conflicts with Lean: Lean wins.
- No placeholder logic or silent fallbacks.
- Prefer small, reviewable changes.

### After Every Change to `KatLang.lean`

After any modification to `lean/KatLang.lean`, you **must**:

1. **Run CoreTests** — execute `lake build CoreTests` from the `lean/` directory and confirm all tests pass (every `#eval` line must print `true`; no `false` or errors).
2. **Check AstDemo** — execute `lake build AstDemo` from the `lean/` directory and confirm it builds without errors. AstDemo exercises the AST constructors directly; a build failure there signals a breaking API change.

Both checks must pass before the change is considered complete. If either fails, fix the failures before proceeding with C# changes.

### After Significant Syntax Changes

After any change to `Lexer.cs` or `Parser.cs` that affects the surface grammar — new expression forms, new pattern kinds, new operators, changes to precedence or associativity, or new token types — review `KatLang.ebnf` and update it to match. Specifically:

- Added or removed a token recognized by the lexer → update terminal rules.
- Added or removed a production in the parser → update the corresponding non-terminal.
- Changed operator precedence or associativity → update the grammar hierarchy.
- Renamed or restructured an AST node that maps to a grammar rule → update the rule and any associated comments.

`KatLang.ebnf` tracks what the parser actually accepts. It is not derived from `KatLang.lean` — surface syntax details (tokenization, concrete notation, punctuation) live only in `Lexer.cs` and `Parser.cs`. Keep all three in sync: `KatLang.lean` (normative semantics), `Parser.cs` (implementation), `KatLang.ebnf` (grammar reference). Drift between any two is a documentation bug.

### After Significant Syntax or Semantic Changes

After any change that affects how KatLang programs are written or how they behave — new syntax forms, changed evaluation rules, new built-in operations, changed error conditions, or new language concepts — review `tutorial.md` and update any affected examples, explanations, or descriptions. Specifically:

- New syntax available to users → add an illustrative example.
- Syntax removed or renamed → remove or correct affected examples.
- Changed evaluation behavior → update the corresponding explanation.
- New error condition or changed error message → reflect it in the relevant section.

`tutorial.md` is the primary user-facing documentation. It must accurately reflect the language as it actually works. Stale examples or incorrect descriptions are bugs.

---

## Required Spec-First Workflow

When implementing features:

1. Locate relevant Lean definitions.
2. Summarize their intent.
3. Define mapping:
   Lean construct → C# AST → parser rule → evaluator rule.
4. List invariants explicitly.
5. Implement minimal complete slice (AST + parser + tests).
6. Validate with positive and negative tests.
7. Summarize diff and explain spec alignment.

If Lean is ambiguous: stop and ask.

---

## Lean → C# Mapping Requirements

When implementing parser features:

- Identify Lean constructors directly.
- Preserve structural distinctions in Lean AST.
- Respect operator precedence and associativity as defined.

### Numeric Mapping

Lean `Int` is interpreted as `decimal` in C# by convention.
If precision issues arise, propose migration strategy — do not silently change behavior.

---

## Scope Control

Default scope is the Lean-defined core only.

Do not add:

- new operators
- implicit coercions
- syntactic sugar
- convenience grammar

Unless already defined in Lean or explicitly requested.

Experimental features must be gated and default to spec-compliant behavior.

---

## C# Implementation Rules

- Use modern C#.
- Prefer immutable AST nodes.
- Encode invariants structurally.
- Parser must be deterministic and total.
- Prefer hand-written recursive descent or Pratt parser.

### Error Handling

- Parsing failures return structured errors.
- Include position and concise explanation.
- Exceptions only for internal invariant violations.

---

## AST Design Standards

- Minimal and semantically meaningful.
- Avoid redundant state.
- Mirror Lean structural distinctions.
- Do not collapse `.dotCall` into `.call` or `.prop` in C# — it must remain explicit.

---

## Testing Requirements

Every feature must include:

1. Parsing success tests.
2. Parsing failure tests.
3. At least one edge case.

Recommended: golden tests asserting:

    KatLang source → normalized AST

Also include semantic tests for `.dotCall` covering:

- Structural property access
- Receiver injection
- Lexical fallback
- Ambiguous imports

---

## Research & Extension Protocol

When proposing new features:

1. Specify change in Lean first.
2. Analyze interactions.
3. Highlight risks.
4. Implement in C# only after confirmation.

If feature not in Lean and no spec change requested:
Do not implement — propose Lean extension plan.

---

## Working Style

For implementation tasks:

1. Summarize Lean anchors.
2. Propose minimal plan.
3. Implement incrementally.
4. Provide concise diff summary.
5. Explain alignment with Lean semantics.

If uncertain, ask — but only after referencing Lean definitions.
