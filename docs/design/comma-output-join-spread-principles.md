# Comma, Grouping, And Spread Principles

This note supersedes the earlier flat stream-composition design notes. Issue #125 changed the model to expression-list slots plus sequence values.

## Current Principles

1. Comma is the global expression-list separator.
2. A bare expression list is consumed by its surrounding syntax: root output consumes it as output slots, call syntax consumes it as argument slots, and `open` consumes its own declaration target list.
3. Parentheses materialize an expression list as one sequence value.
4. Same-line adjacency acts as an implicit comma where an expression list is already open, so `1 2 3` behaves like `1, 2, 3` in those contexts. A newline is a different mechanism — a body/statement/output boundary, not a global implicit comma. At root output that boundary still yields separate slots (so `1`/`2`/`3` on three lines are three output slots), but in a simple one-line definition body a newline ends the body rather than extending the list.
5. Semicolon is not supported as expression syntax. It is not an alternative separator or sequence constructor.
6. Use parentheses to materialize one sequence value. Therefore `(1, 2, 3)` is one value, while `1, 2, 3` is three surrounding slots.
7. `...` is unary postfix spread. It opens ONE item-producing boundary of its immediate operand's evaluated value and contributes the opened items to the surrounding item supply — it does not create or emit a sequence value by itself. Sequence values and exact list values supply their contained items; other values follow the total item-view rule (an atom or string supplies itself as one item). It never consumes a right operand.
8. Top-level user variadic/rest parameters consume the function-call argument supply **as supplied**. Fixed captures bind from the front and back, and the one movable rest captures the remaining middle arguments as a canonical grouped sequence value. Inline comma/adjacency items (`G(1, 2, 3)`), explicitly opened values (`G(A...)`), empty input (`G()`), and one unspread grouped sequence value (`G(A)` or `G((1, 2, 3))`) are all valid but retain their call-boundary distinction: the unspread sequence is one argument, while `A...` supplies its immediate items. Rest-only functions can display the same value for both paths because canonical capture of one sequence argument collapses redundant sequence structure; mixed fixed/rest shapes expose the difference. Multiple sibling grouped values are preserved unless explicitly opened with `...`. This binding is distinct from three neighbouring behaviors:
   - **Collection builtins** (`filter`, `map`, `count`, `sum`, and the rest) do NOT use item-supply binding: they are ordinary fixed-arity callables with one fixed `collection` parameter plus fixed control parameters (`sum(collection)`, `contains(collection, item)`), so `sum(1, 2, 3)` and `count(Values...)` are ordinary arity errors. The bound collection value is interpreted through the post-binding one-level collection view (a lone sequence or exact list opens; a scalar is a one-element collection). Item-supply binding remains a USER-function mechanism.
   - **Expression-side `value...`** (principle 7) explicitly opens one sequence or list boundary and contributes the items to the surrounding item supply.
   - **Single-name value capture** (`c = A`) preserves sequence boundaries; it binds the whole value without opening it.
9. Dot-call receiver syntax remains canonical call syntax: `receiver.Property(args...)` means `Property(receiver, args...)`, not `Property(receiver..., args...)`.
10. `open` remains declaration syntax with its dedicated comma-only target grammar; it does not use ordinary expression-list or spread syntax.
11. Square brackets materialize an expression list as one EXACT immutable list value — a second materialization form beside principle 3's parentheses, with the opposite canonicalization contract: no singleton or empty erasure ever applies to list structure (`[7] != 7`, `[[]] != []`, `[] != ()`), while ordinary parentheses around a list stay redundant sequence grouping (`([1, 2]) == [1, 2]`). Element slots use the ordinary expression-list model including spread (`[0, A..., 4]`). Spread (principle 7) opens exactly one boundary of either collection kind (`[1, 2, 3]...` supplies three items; `[]...` supplies zero). USER-call item-supply binding (principle 8) does NOT extend to lists: a list stays one opaque supplied argument at user-call boundaries unless `...` is written. The POST-BINDING builtin collection view, by contrast, opens one outer boundary of the bound sequence OR list collection argument (`count([1, 2, 3])` is 3) — never recursively, and never before ordinary fixed binding — and collection-producing builtins materialize exact list results (`take`, `skip`, `filter`, `map`, `order`, `orderDesc`, `distinct`, `range`), while variadic/rest capture stays canonical and sequence-shaped. The lone-structure opening of assignment deconstruction treats a lone list like a lone sequence (`x, y, z = [1, 2, 3]` opens), and its rest captures stay sequence-shaped. Indexing `:` opens its TARGET the same way (the projection target view): `[1, 2, 3]:0` selects one immediate element under identical zero-based index rules as sequence selection, and the selected element is returned exactly as stored (a selected list element stays one exact list). `[` always begins a new expression (never a call/indexing delimiter), so `A[1]` is the adjacency list `A, [1]`.

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
