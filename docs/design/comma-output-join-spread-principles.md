# Comma, Grouping, And Spread Principles

This note supersedes the earlier flat stream-composition design notes. Issue #125 changed the model to expression-list slots plus sequence values.

## Current Principles

1. Comma is the global expression-list separator.
2. A bare expression list is consumed by its surrounding syntax: root output consumes it as output slots, call syntax consumes it as argument slots, and `open` consumes its own declaration target list.
3. Parentheses materialize an expression list as one sequence value.
4. Same-line adjacency acts as an implicit comma where an expression list is already open, so `1 2 3` behaves like `1, 2, 3` in those contexts. A newline is a different mechanism — a body/statement/output boundary, not a global implicit comma. At root output that boundary still yields separate slots (so `1`/`2`/`3` on three lines are three output slots), but in a simple one-line definition body a newline ends the body rather than extending the list.
5. Semicolon is not supported as expression syntax. It is not an alternative separator or sequence constructor.
6. Use parentheses to materialize one sequence value. Therefore `(1, 2, 3)` is one value, while `1, 2, 3` is three surrounding slots.
7. Expression spreading is the reserved named intrinsic `spread : Value -> Supply`. Its call-shaped `spread(value)` and extension-property-shaped `value.spread` spellings both contribute ONE item-producing boundary of the operand's evaluated value directly to the surrounding item supply; neither spelling calls a user function, returns a value, or creates a sequence/list. Sequence values and exact list values supply their contained items; other values follow the total item-view rule (an atom or string supplies itself as one item). A spread expression never consumes a right operand. The `...` token is not expression syntax: it is the postfix marker of a collecting binding (`name...`) only.
8. Top-level user variadic parameters consume the function-call argument supply **as supplied**. Fixed captures bind from the front and back, and the one movable variadic parameter COLLECTS the matched middle arguments as one exact immutable list (`collect`): zero slots form `[]`, one slot forms `[item]` (never erased), many form `[a, b, ...]`. Inline comma/adjacency items (`G(1, 2, 3)` collects `[1, 2, 3]`), explicitly spread values (`G(A.spread)`), empty input (`G()` collects `[]`), and one unspread grouped value (`G(A)` or `G((1, 2, 3))` collects `[A]`) are all valid but retain their call-boundary distinction: the unspread structure is one argument and one collected element, while `A.spread` supplies its immediate items. Grouped and spread calls are observably different for every sequence-valued, list-valued, and empty argument (the old single-variadic display coincidence via singleton collapse is superseded — July 2026 collecting-binding change); only scalar atom/string arguments coincide, because spread is total (`7.spread` supplies `7` itself, principle 7). Forwarding a collected list is ordinary spread (`Target(items.spread)` re-supplies exactly the collected items: `spread(collect(xs)) = xs`). Multiple sibling grouped values are preserved unless explicitly passed through `spread`. This binding is distinct from three neighbouring behaviors:
   - **Collection builtins** (`filter`, `map`, `count`, `sum`, and the rest) do NOT use item-supply binding: they are ordinary fixed-arity callables with one fixed `collection` parameter plus fixed control parameters (`sum(collection)`, `contains(collection, item)`), so `sum(1, 2, 3)` and `count(Values.spread)` are ordinary arity errors. The bound collection value is interpreted through the post-binding one-level collection view (a lone sequence or exact list opens; a scalar is a one-element collection). Item-supply binding remains a USER-function mechanism.
   - **Expression-side `value.spread`** (principle 7) is the spread expression: it contributes the items of one sequence or list boundary to the surrounding item supply.
   - **Single-name value capture** (`c = A`) preserves sequence boundaries; it binds the whole value without opening it.
9. Dot-call receiver syntax remains canonical call syntax: `receiver.Property(C, D)` means `Property(receiver, C, D)`, not `Property(receiver.spread, C, D)`. The receiver is one leading argument boundary unless the source explicitly applies `spread`.
10. `open` remains declaration syntax with its dedicated comma-only target grammar; it does not use ordinary expression-list or spread syntax.
11. Square brackets materialize an expression list as one EXACT immutable list value — a second materialization form beside principle 3's parentheses, with the opposite canonicalization contract: no singleton or empty erasure ever applies to list structure (`[7] != 7`, `[[]] != []`, `[] != ()`), while ordinary parentheses around a list stay redundant sequence grouping (`([1, 2]) == [1, 2]`). Element slots use the ordinary expression-list model including spread (`[0, A.spread, 4]`). Spread (principle 7) opens exactly one boundary of either collection kind (`[1, 2, 3].spread` supplies three items; `[].spread` supplies zero). USER-call item-supply binding (principle 8) does NOT extend to lists: a list stays one opaque supplied argument at user-call boundaries unless an explicit `spread(value)` / `value.spread` slot opens it. The POST-BINDING builtin collection view, by contrast, opens one outer boundary of the bound sequence OR list collection argument (`count([1, 2, 3])` is 3) — never recursively, and never before ordinary fixed binding — and collection-producing builtins materialize exact list results (`take`, `skip`, `filter`, `map`, `order`, `orderDesc`, `distinct`, `range`), and variadic/collecting binding collects the SAME exact-list kind (principle 8). The lone-structure opening of assignment deconstruction treats a lone list like a lone sequence (`x, y, z = [1, 2, 3]` opens), and its collecting targets collect exact lists too (`x, rest... = [1, 2, 3]` binds `rest = [2, 3]`). Indexing `:` opens its TARGET the same way (the projection target view): `[1, 2, 3]:0` selects one immediate element under identical zero-based index rules as sequence selection, and the selected element is returned exactly as stored (a selected list element stays one exact list). `[` always begins a new expression (never a call/indexing delimiter), so `A[1]` is the adjacency list `A, [1]`.

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
