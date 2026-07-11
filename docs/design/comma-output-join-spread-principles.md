# Comma, Grouping, And Spread Principles

This note supersedes the earlier flat stream-composition design notes. Issue #125 changed the model to expression-list slots plus sequence values.

## Current Principles

1. Comma is the global expression-list separator.
2. A bare expression list is consumed by its surrounding syntax: root output consumes it as output slots, call syntax consumes it as argument slots, and `open` consumes its own declaration target list.
3. Parentheses materialize an expression list as one sequence value.
4. Same-line adjacency acts as an implicit comma where an expression list is already open, so `1 2 3` behaves like `1, 2, 3` in those contexts. A newline is a different mechanism — a body/statement/output boundary, not a global implicit comma. At root output that boundary still yields separate slots (so `1`/`2`/`3` on three lines are three output slots), but in a simple one-line definition body a newline ends the body rather than extending the list.
5. Semicolon is not supported as expression syntax. It is not an alternative separator or sequence constructor.
6. Use parentheses to materialize one sequence value. Therefore `(1, 2, 3)` is one value, while `1, 2, 3` is three surrounding slots.
7. `...` is unary postfix spread. It spreads the evaluated sequence value of its immediate operand into the surrounding structural context and never consumes a right operand.
8. Top-level user variadic/rest parameters consume **item supplies** with singleton-boundary normalization: if the supplied item supply is exactly one grouped sequence value, the matcher may consume that value's contents as the item supply, repeating through singleton boundaries. Inline comma/adjacency items (`G(1, 2, 3)`), explicitly opened values (`G(A...)`), empty input (`G()`), and one grouped sequence value (`G((1, 2, 3))`) are all valid inputs. Multiple sibling grouped values are preserved unless explicitly opened with `...`. This binding is distinct from three neighbouring behaviors:
   - **Sequence builtins** (`filter`, `map`, `count`, `sum`, and the rest) expose rest-shaped public signatures (`sum(values...)`, `contains(values..., item)`) and use this **same** item-supply binding: the rest captures the collection (with singleton-boundary normalization), suffix parameters bind from the back, and sibling grouped values are preserved unless opened. A builtin that truly needs one collection value declares a non-rest `values` parameter instead.
   - **Expression-side `value...`** (principle 7) explicitly opens one sequence value into the surrounding structural context.
   - **Single-name value capture** (`c = A`) preserves sequence boundaries; it binds the whole value without opening it.
9. Dot-call receiver syntax remains canonical call syntax: `receiver.Property(args...)` means `Property(receiver, args...)`, not `Property(receiver..., args...)`.
10. `open` remains declaration syntax with its dedicated comma-only target grammar; it does not use ordinary expression-list or spread syntax.

## Examples

```katlang
1, 2, 3              // three output slots at root
1 2 3                // also three output slots where adjacency is allowed
(1, 2, 3)            // one sequence value
1, (2, 3)            // two output slots: atom 1 and sequence value (2, 3)
(1, 2), 3            // two output slots: sequence value (1, 2) and atom 3
F(1, 2, 3)           // three call argument slots
F((1, 2, 3))         // one sequence argument
F((1, 2, 3), (4, 5, 6)) // two call arguments, each a sequence value
```

Table-like output uses sequence-value rows:

```katlang
Reports = (7, 6, 4, 2, 1),
          (1, 2, 7, 8, 9),
          (9, 7, 6, 2, 1)
```

Without row parentheses this is one flat expression list. Use one parenthesized value per row when a sequence of row values is intended.
