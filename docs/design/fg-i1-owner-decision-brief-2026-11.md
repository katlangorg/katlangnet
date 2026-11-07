# FG-I1: owner decision brief, production identity obligation (November 7, 2026)

**FG-I1 remains open.** No theorem establishes the original production-use-site obligation for all
admitted programs. This deliverable is the decision-brief alternative in the task, independently
reviewed and corrected. The production comparator and observable semantics are unchanged.

## What is proved, and what is missing

The repeated-name permutation laws require `CallableTransOn` on their contribution lists.
`production_head_walk_follows` derives it from `ModelFollows`; `model_follows_of_heap` derives that
premise from `HeapFollows`. Neither is established for arbitrary production runs. Publication
preservation still assumes that the projection's intermediate heap and returned identity follow
the table; the construction lemmas retain their table, freshness and `SitePresence` premises.

An unconditional whole-heap `PresenceTable` invariant is too strong: admitted shared host graphs
can publish one declaration under both identified and anonymous parents. A group-local invariant
would have to accommodate such inputs, or justify a narrower domain at the actual use site without
restricting admission or assuming the desired comparison law.

`CallableIdentityClosure.lean` proves the following, with standard axioms only:

| Result | Exact scope |
| --- | --- |
| `sameScopeVia_printed`, `sameIdentityVia_printed` | The parameterized comparators equal production when their fallback is `printed` |
| `fork_identity_ab`, `fork_identity_bc`, `fork_identity_ac` | For a `CallableFork`, two identity verdicts are printed comparisons; the identified outer pair is false |
| `use_site_is_a_printer_fact` | For any list **containing all three** fork identities, `CallableTransOn` implies that the two mixed printed equalities do not both hold |
| `success_aligned_fork_iff` | Under the stated parent-misalignment premise, `SuccessAligned` on one fork pair is exactly its printed inequality |
| `some_fallback_is_intransitive` | With the additional stated outer-pair refusal, replacing the fallback by accept-all makes the fork intransitive |

These results obstruct an argument using only fork structure and no information about the fallback.
They do **not** prove every group-local approach impossible, full `ReprSeparatesPresence` necessary
for transitivity, or a reachable nontransitive triple for the actual printer.

The current proof chain has no kernel proof of the required printed inequalities. In the pinned
Lean library, `Format.pretty` calls `prettyM`, which calls the opaque `partial` layout loop `be`.
Simple `rfl`/`decide` probes fail even on `(Format.text "a").pretty = "a"`. That diagnoses the current
reduction barrier; failed tactics are not a general impossibility theorem. A certified printer
interface or another production invariant remains a possible research route, with no closure
claimed here.

## Reachability evidence and its limits

The guards execute actual public `runResultM` programs; they are finite runtime evidence, not
kernel proofs of reachability or quantified production invariants.

- HP-14s publishes a mixed-presence pair, but its depths are 2 and 3. `compatibleActivations`
  refuses it independently of the printer. The earlier contrary explanation is corrected.
- HP-14t supplies one shared block under host 0, the anonymous prelude, and host 1, all at equal
  depth. `equalDepthFork` reaches a decisive mixed comparison and fails with a callable conflict
  after publishing two identities. The third contribution is **not** inspected. The generated
  C#/Lean differential artifact pins `err type` for the encoded host tree.
- The separate Lean `allThree` program invokes three **distinct** parameters and publishes all
  three identities in one heap; its executable `isFork` check succeeds. It does not complete a
  repeated-name group containing all three. `kernel_fork` separately constructs an inhabitant of
  `CallableFork`; it is not a theorem equating those terms with a reachable heap.
- No reachable nontransitive triple is known. The real printer refuses the mixed pairs checked.
  A source-only nested dotted-open example (`midOwnedDottedOpen`) also reaches a mixed decision in
  contextual wiring according to the implementer's instrumented experiment. Its checked-in guards
  pin the outcome and a separate wrapper example, not the internal decision trace.

## Owner alternatives

| Option | Change and remaining work | Semantic consequences |
| --- | --- | --- |
| **A: reject mixed presence (recommended for evaluation)** | Make mixed pairs false in `sameDeclaringScope`; retain printing for two anonymous levels. The proof-only `candidate_identity_trans` and `candidate_scope_presence` already remove the transitivity/provenance and presence premises for that candidate. Integrate and repair production corollaries, then validate and review | Universal comparator equality holds **iff** `ReprSeparatesPresence` (`candidate_eq_production_iff`). That is sufficient for unchanged program behaviour, not a necessary-and-sufficient observational theorem. C# already distinguishes these levels by identity |
| B: fully structural fallback | Define a total equality on `ScopeCtx.declaration` and its mutually nested AST payloads, and prove its laws. This removes printing from fallback decisions entirely; no implementation is delivered | Equality of declarations implies equal printed text already. To preserve every fallback verdict, the converse must hold on fallback-domain declarations: no printer collision between structurally unequal declarations. This is stronger on anonymous pairs than A, and is unproved |
| C: retain the comparator | Keep the conditional theorems. Investigate a certified printer interface or a group-local production invariant that proves the needed use-site facts independently | No semantic change; FG-I1 stays open until that work succeeds. No proof of impossibility is claimed |
| D: restrict admitted host graphs | Exclude the shared fork inputs | Changes admitted programs, is excluded by the task, and does not itself discharge contextual wiring's source-only `SitePresence` premise |

If A encounters an equal-text mixed pair, it changes that verdict from true to false. Potential
consumers include repeated-name acceptance, open-provider deduplication/ambiguity, accessibility,
and `activeDeclaration?`'s choice of declaring activation. B could additionally change anonymous-pair
verdicts on a printer collision. No such observable counterexample has been demonstrated. Reading
the derived printer suggests that its final `none`/`some` identity field separates presence, but
this remains an implementation argument, not a kernel theorem.

**No authorization to change the comparator is inferred.** A and B require an owner decision. An
unchecked printer axiom is excluded; `native_decide` is not a quantified printer proof and would
add a dependency outside the pinned three-axiom audit.

## Evidence and acceptance boundary

The implementer tested A in the ignored scratch copy `artifacts/fg-i1/closure/candidate-lean`:
`CoreTests`, `SemanticExplorerCases`, `LanguageSpecCases`, and `AstDemo` built (61 jobs). The proof
target failed at fallback-dependent proofs; no repaired full proof build was completed. This is
inherited exploratory evidence, not validation of an integrated comparator change.

This independent review checks the delivered main checkout with the repository's full V3 procedure;
its command, exit codes, totals and logs are recorded in the coordination result. The earlier
97-test/two-target run is not reused as reviewer validation. Even a green V3 result validates this
conditional decision brief and its current guards; it does not discharge FG-I1.

After choosing A or B, deliver the authorized production change and repaired proofs here, connect
the unconditional identity result to the actual binder, update ledger E-8a, and complete V3 plus
independent review before marking FG-I1 complete. `ProdRel`, `Fits`, and `RepeatedPlainList` are
separate obligations and must remain explicit.
