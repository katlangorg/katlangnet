# KatLang Project Instructions

## Project Overview

- KatLang core semantics are specified in `lean/KatLang.lean`.
- The C# implementation in `src/KatLang/` must follow Lean.
- If Lean and C# are both wrong for the same bug, fix both together.
- Do not invent syntax or semantics that are not in Lean unless explicitly instructed.
- Keep this file concise and operational, not a design document.

## Core Rules

### Source of truth

- `lean/KatLang.lean` is the authoritative source for KatLang core semantics and invariants.
- Lean wins over implementation convenience, performance, or stylistic preference.
- If Lean is ambiguous for the requested change, stop and clarify before implementing.
- Maintain Lean -> C# alignment for parser, elaboration, evaluator, and editor-visible behavior.

### Scope control

- Default scope is the Lean-defined language plus the existing front-end/editor pipeline.
- Do not add:
   - new operators
   - convenience syntax
   - implicit coercions
   - hidden fallbacks
   - AST simplifications that erase Lean distinctions
- If a requested feature is not in Lean, propose the Lean change first instead of implementing it directly.

### Structural fidelity

- Preserve structural distinctions in AST and runtime behavior.
- `.dotCall` is first-class in Lean and must remain explicit in C#.
- `open` is part of algorithm definition structure and must follow the current parser/elaboration/runtime model.
- `Output = expr` is reserved result syntax, not an ordinary property definition.

### Optimization boundary

- C# evaluator memoization is an implementation optimization boundary.
- It is not a Lean-level KatLang semantic feature unless Lean is explicitly extended to make it one.
- Do not describe KatLang as lazy, memoized, or call-by-need based on the current evaluator optimization.

### Diagnostics and fallbacks

- Keep parser and elaboration errors structured and source-positioned.
- Do not add silent recovery paths or hidden semantic fallbacks.
- If behavior is intentionally implementation-only, keep that boundary explicit.

## Repository Map

- `lean/KatLang.lean`
   - authoritative core spec
   - core AST, evaluation rules, invariants, and semantic intent
- `lean/CoreTests.lean`
   - Lean regression checks
- `lean/AstDemo.lean`
   - direct AST-construction compatibility check
- `src/KatLang/`
   - C# AST, parser, elaboration, evaluator, diagnostics, and public APIs
- `src/KatLang/Semantics/`
   - editor tooling only; not the evaluator and not normative language semantics
- `.github/agents/katlang-generator.agent.md`
   - custom agent for generating valid, runnable KatLang from natural-language requests
   - must stay aligned with current syntax, builtin usage, `Output` rules, and code-generation idioms
- `tests/KatLang.Tests/`
   - parser, evaluator, elaboration, semantics, and integration regression coverage
- `KatLang.ebnf`
   - documents the actual accepted surface grammar and must match lexer/parser behavior
- `tutorial.md`
   - main user-facing documentation and must match real language behavior

## Semantics Folder

- `src/KatLang/Semantics/` derives editor-facing semantic information from parsed and elaborated AST.
- It is used for:
   - go-to-definition
   - find references
   - hover
   - semantic classification
   - declaration and resolution lookup
   - callable-property metadata
- Build semantic models from `Parser.Parse` output, not raw syntax.
- Only source-backed identifier tokens may produce semantic sites, spans, occurrences, or resolutions.
- Synthetic constructs must not invent source spans.
- This layer reflects editor-visible meaning; it does not define core language semantics.

### Update Semantics when editor-visible meaning changes

- AST spans or declaration spans
- lookup behavior
- `open` behavior
- dot-call lookup or fallback behavior
- explicit or implicit parameter handling
- conditional binders
- builtins, preludes, or intrinsic metadata
- callable-property shape
- reserved-name or builtin classification

### Required test sync

- When `src/KatLang/Semantics/` changes, update `tests/KatLang.Tests/SemanticModelTests.cs`.
- Preserve exact source-span invariants for editor-facing behavior.

## Important Current Semantic Realities

### dotCall

- `.dotCall` is a core Lean concept, not just surface sugar.
- Dot-call behavior in Lean, parser, evaluator, and Semantics must stay aligned.
- Structural property lookup, receiver injection, lexical fallback, and diagnostics must remain consistent across layers.

### open

- `open` is part of algorithm definition structure and affects both runtime and editor behavior.
- Runtime and Semantics must match the current parser and elaboration rules for `open`.
- `open Name` may target a lexically visible private head, but opens still expose only public members.
- `open 'url'` is front-end sugar, not a core AST construct.
- Unresolved `load` forms should not survive into semantic modeling.

### Output and load boundary

- `Output = expr` is reserved result syntax and direct calls do not delegate through structural `Output`.
- External `Algo.Output` and `Algo.Output(...)` are invalid.
- Default parse/run entry points reject unresolved `load`; only elaboration-enabled paths should consume it.

### Conditional algorithms

- Conditional algorithms are an active and high-risk area.
- Changes to branch shape, binder scoping, higher-order behavior, callable-property shape, or lowering rules must be handled consistently across:
   - Lean
   - parser and elaboration
   - evaluator
   - `src/KatLang/Semantics/`
   - tests
   - docs

### Builtins and intrinsic metadata

- Builtins, prelude exposure, and editor-visible intrinsic metadata must stay synchronized where relevant across:
   - evaluator
   - parser and elaboration assumptions
   - Semantics
   - tests
   - `.github/agents/katlang-generator.agent.md`
   - docs

### Numeric reality

- Lean core uses `Int`.
- C# currently uses `decimal` as the runtime numeric representation.
- Do not silently widen or reinterpret numeric behavior without checking Lean first.

## Required Sync Rules

### After Lean changes

From `lean/` run:

1. `lake build CoreTests`
2. `lake build AstDemo`

Both must pass before the change is complete.

### After syntax changes affecting lexer or parser grammar

- Review and update `KatLang.ebnf`.
- Keep grammar documentation aligned with actual accepted surface syntax, including tokenization, precedence, associativity, and parser-only surface forms.

### After significant syntax or semantic changes

- Review and update `tutorial.md`.
- Keep examples and explanations aligned with actual language behavior.

### After KatLang generation-rule changes

- Review and update `.github/agents/katlang-generator.agent.md` when syntax, builtins, `Output` rules, `open`/`load` behavior, or recommended KatLang code-generation idioms change.

### After Semantics or editor-visible changes

- Update `tests/KatLang.Tests/SemanticModelTests.cs`.
- Add or adjust coverage for spans, declarations, resolutions, classification, and property metadata when affected.

### General rule

- If a change affects multiple layers, update all affected layers in the same task when feasible.
- Prefer small, reviewable changes.

## Working Style

### Before implementing semantic changes

- Check Lean anchors first.
- Identify the relevant Lean constructors, invariants, and evaluation rules.
- Map the change across:
   - Lean construct
   - C# AST or front-end representation
   - parser and elaboration behavior
   - evaluator behavior
   - Semantics or editor behavior
   - tests and docs

### Implementation expectations

- Maintain Lean -> C# alignment.
- Preserve structural distinctions in AST.
- Keep diagnostics structured and source-positioned.
- Do not add convenience syntax or hidden fallbacks.
- Keep implementation choices explainable in terms of Lean.

### Testing expectations

- Add or update focused tests for the changed behavior.
- Include negative coverage when behavior has meaningful failure modes.
- Prefer tests near the changed layer.
- If behavior is cross-cutting, cover parser, evaluator, Semantics, and docs as needed.

### Practical defaults

- Prefer small, reviewable changes.
- If a change is only an optimization, say so explicitly.
- Push detailed edge-case knowledge into code comments and tests rather than expanding this file.
- When updating this file in future, prefer shortening and de-duplicating over expanding.
