# KatLang Agent Instructions

## Project Overview

- These instructions are for Codex and other AI coding agents working in this repository.
- `AGENTS.md` is the canonical shared agent-instructions file for this repo.
- KatLang's authoritative language model is `lean/KatLang.lean`.
- The C# implementation in `src/KatLang/` must stay semantically aligned with Lean.
- If Lean and C# are both wrong for the same bug, fix both together when feasible.
- Keep this file operational and concise.

## Core Architecture

- `lean/KatLang.lean`: source of truth for AST shape, evaluation rules, and invariants.
- `lean/CoreTests.lean`, `lean/AstDemo.lean`: Lean-side regression and AST compatibility checks.
- `src/KatLang/`: C# AST, parser, front-end elaboration, evaluator, diagnostics, and public API.
- `src/KatLang/Semantics/`: editor-facing semantic tooling only; it is not the evaluator and not the normative semantics layer.
- `tests/KatLang.Tests/`: parser, evaluator, elaboration, semantics, and integration regression coverage.
- `tutorial.md`, `KatLang.ebnf`, and generator prompt/agent files must stay aligned with real language behavior.

## Language Semantics And Design Rules

- Lean 4 wins over implementation convenience, performance, or stylistic preference.
- If Lean is ambiguous for a requested behavior change, stop and clarify before implementing.
- Do not invent syntax or semantics that are not in Lean unless the task explicitly includes the Lean change.
- Do not add new operators, convenience syntax, implicit coercions, hidden fallbacks, or AST simplifications that erase Lean distinctions.
- Preserve structural distinctions in the AST and runtime model. In particular, `.dotCall`, `open`, and `Output = expr` are language-level constructs, not incidental parser sugar.
- `Output = expr` is reserved result syntax. `Algo.Output` and `Algo.Output(...)` are invalid.
- Ownership-first lookup is fundamental. Keep lookup behavior aligned across evaluator, parser/front-end elaboration, parameter detection, and semantic tooling.
- `open Name` may target a lexically visible private head, but `open` only exposes public members.
- `open 'url'` is front-end sugar for load elaboration, not a core AST construct.
- Dot-call uses structural lookup first and lexical fallback second. Structural lookup, receiver injection, fallback order, and diagnostics must stay consistent across Lean and C#.
- Ordinary lexical dot-call passes the receiver as one leading argument boundary. `A.B(C, D)` means `B(A, C, D)`, not a call where `A`'s top-level values are spread before `C` and `D`.
- Only sequence/variadic builtin dot-call paths may opt into receiver top-level expansion, and that expansion must remain explicit in builtin metadata/evaluator handling.

## Lean/C# Consistency Requirements

- `Parser.Parse(...)` and `ParseResult` are elaborated front-end outputs, not raw syntax trees.
- The raw syntax boundary is `Parser.ParseSyntax(...)`.
- `FrontEndPipeline.Process(...)` is the explicit C# front-end path for elaboration passes such as load elaboration, parameter detection, implicit argument resolution, and property exposure resolution.
- Default parse/run entry points reject unresolved `load`; only elaboration-enabled paths may consume it.
- When semantics change, update all affected layers together: Lean, C# parser/elaboration/evaluator, `src/KatLang/Semantics/`, tests, and user-facing docs.
- Avoid duplicating semantic rules across parser, evaluator, parameter detection, and semantic model code. Reuse the owning logic when possible.
- C# evaluator memoization is an implementation optimization boundary, not a Lean-level language feature.
- Lean core numeric semantics use `Int`; the current C# runtime uses `decimal`. Do not silently widen or reinterpret numeric behavior without checking Lean first.

## Builtins And Sequence/Combining Conventions

- `arity` means the structural count of top-level output slots.
- `count` means the number of evaluated top-level values.
- Do not treat `arity` and `count` as interchangeable.
- Semicolon `;` is the structural combining operator, not a normal argument separator.
- Comma `,` separates output slots and call arguments.
- This convention especially matters for sequence builtins such as `filter`, `map`, `order`, `orderDesc`, `count`, `first`, `last`, `min`, `max`, `sum`, `avg`, and `reduce`.
- Sequence builtins and combining behavior must stay consistent across Lean and C#.
- Keep plain-call and dot-call sequence behavior aligned, including receiver expansion rules and grouped-value behavior.
- Changes to builtins, preludes, or intrinsic metadata may require synchronized updates in evaluator, front-end assumptions, semantics, tests, tutorial, and generator guidance.

## Editor Semantics

- `src/KatLang/Semantics/` derives editor-facing meaning from parsed and elaborated ASTs.
- Build semantic models from `Parser.Parse(...)` / `ParseResult`, not from raw syntax.
- Only source-backed identifiers may produce semantic sites, resolutions, declarations, or spans.
- Synthetic constructs must not invent source spans.
- If editor-visible behavior changes, update `src/KatLang/Semantics/` and `tests/KatLang.Tests/SemanticModelTests.cs` together.
- Preserve exact source-span invariants for hover, references, go-to-definition, classification, and callable-property metadata.

## Testing Expectations

- Prefer minimal, semantics-preserving, reviewable changes.
- Add or update focused tests near the changed layer.
- Include negative coverage when failure modes are meaningful.
- When changing language behavior, update Lean tests and C# tests together.
- If a change crosses parser, evaluator, semantics, or docs boundaries, cover the affected layers in the same task when feasible.

## Documentation Expectations

- Update `KatLang.ebnf` when lexer/parser grammar changes.
- Update `tutorial.md` when user-facing behavior changes.
- Update generator-facing files when syntax, builtins, `Output`, `open`/`load`, or recommended code-generation idioms change.
- In this repo that usually includes `.github/agents/katlang-generator.agent.md` and any related generator prompt assets.

## Coding Guidance

- Prefer small changes that fix the root semantic issue without widening scope unnecessarily.
- Do not introduce new AST shapes unless strongly justified by Lean or an existing architectural boundary.
- Preserve the current parser/evaluator/tooling boundaries instead of re-encoding the same rule in multiple places.
- Keep diagnostics structured, source-positioned, user-friendly, and phrased in KatLang terms.
- If a change is implementation-only optimization, say so explicitly.

## Validation

- Run `dotnet test` for the C# regression suite.
- For Lean changes, from `lean/` run `lake build CoreTests` and `lake build AstDemo`.
- No additional demo or web build command is currently documented here; do not invent one.

## Do Not

- Do not silently change language semantics.
- Do not let Lean and C# diverge.
- Do not treat `AGENTS.md` as a long design essay.
- Do not let multiple agent-instruction files drift into conflicting guidance.
- Do not add convenience syntax, hidden fallbacks, or duplicated semantic logic just to make a local change easier.
