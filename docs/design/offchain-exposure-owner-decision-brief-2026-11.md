# Off-chain exposure lookups: owner decision brief (November 27, 2026)

**Recommend approving C's lookup-site rule.** When a reader reaches a written check inside a member, charge the requirement only where the reader's chain and the member's declaring scope share the required owner. Reusing a settlement must give the same classification as settling that check afresh. This decision would allow one currently refused call to return `1`, and would make one currently successful read of `7` fail at the outer member. The two programs below are the compatibility decision. Implementing the rule, including the conditions for safely sharing an answer, is a separate step.

If today's classifications must be preserved, retain A. B can recover component equations for a provably independent component, but the prototype's passing comparisons do not establish a general replacement for the guard. Neither the chain nor the branching terminal benefits from B.

Reviewed on `main` at `22dd3dd4`, from the witnesses that `5d747bb8` preserved in `ExposureResidualReuseTests` (follow-up of the MODA task `aa12a242`). Production, Lean and the Constitution keep the current contract until the owner decides. [Current rule](language-rules/evaluator-and-hosting.md) (THE OFF-CHAIN GAP, THE OFF-CHAIN TERMINAL) · [Q1–Q3 check sites](language-rules/ownership-and-lookup.md) (EACH CHECK IS CHARGED WHERE THE EVALUATOR MAKES IT) · [RES-08](../constitution/constitution.md#res-08--visibility-selects-accessibility-is-checked-on-the-selected-member-afterwards-k1-08) · [Lean/C# alignment](../../dotnet/src/KatLang/SEMANTIC-ALIGNMENT.md)

## The current contract

Since owner decision Q1 (2026-11-14, `73d6256e`), an owner-qualified requirement whose owner is on no level of the settlement site's chain charges nothing and raises no landing. The off-chain observation propagates through nested and reused settlements. A walk fixed to its own consulted level bounds that observation (`Frame.SiteIsItsLevel`). A shareable settlement still marked `Settled.OwnerOffChain` is eligible only under its exact key (content, level, bound owners). That key omits the asking site. Independently, when a frame reports `LookedUpOffChain`, `SettlementShare.SawOffChainLookup` holds for the rest of the resolution. It stops component equations (`PendingResolution.SeedFrame` and `SeedBody`) and path parts (`TakesPathParts`, `TryKeptPathPart`, `KeepPathPart`). Each eager compile and each deferred materialization runs its own resolution.

The rule document records why. The exact-key share's site-free entries can depend on the order of settlements. Any reuse past the exact key skips nested exact stores, and so changes the metadata of programs in which the gap shows.

## What the live rules already say

RES-08's qualification: when the owner of a parameter that a check needs is not a static ancestor of the scope where the check is made, the check can never pass. "It is an error of the path that makes it, when that path runs, and never a requirement of the algorithm around it." The approved check-site rule (Q1–Q3) charges "(a) a written dot path at the READING site" and "(d) a VALUE crossing of a transparent reference in the reference's OWN scope". Rules (b) and (d) are implemented through `CheckSite`. Rule (a) is not implemented for paths written inside a member body that a reader navigates into. On this route, the member's seed initially inherits the outer reader's site. A written dot path inside that body can consequently be charged to an owner that its evaluator check cannot reach.

That one implementation gap produces three observable effects. The check-site rule removes all three.

1. A check that can never pass is charged to a reader inside the owner when the reader's settlement computes it afresh. This contradicts RES-08. The census already records this divergence for its re-entry readers (`census-gaps.txt`, M2 `model-false-admission`, "the open owner question of 0a1718d2").
2. The same check charges nothing when the reader takes an exact-key answer that an earlier off-chain settlement stored. Whether it is charged therefore depends on the reader's key: `H = K.M(1)` and `H(y) = K.M(1) + y` are classified differently.
3. An exact-key answer from a detached read also hides a requirement that can pass. An unrelated root declaration can flip a member's classification and a run's outcome.

## Witnesses

Save either program as `example.kat` and run `katlang run example.kat` using the CLI from this checkout.

```katlang
F(y) = {
A = y + 1
public H(k) = Box.R + k
H(1)
}
Box = { public R = if(false, F.A, 0) }
F.H(1)
```

`Box.R` is exported. The current resolver gives `H` a capture of `y@0`, so the evaluator refuses the outer call at line 7, column 1 with `LocalOnlyProperty(H)`. B preserves that result. C exports `H` and returns `1`. Replacing the last line with `F(5)` returns `1` today, and replacing it with `Box.R` returns `0`.

```katlang
F(x) = {
public G = x + 1
public W = F.G
public X = [W, 7][1]
X
}
R = F.W
F.X
```

The read of `F.G` inside `W` can use an activation of `F`. Today the unrelated declaration of `R` causes both `W` and `X` to be published as exported, and the program returns `7`. B preserves that result. C gives both properties the capture `x@0` and reports `LocalOnlyProperty(X)` at line 8, column 1. Deleting the `R` line produces the same refusal on line 7 today.

The table gives the remaining controls from the Release probe at `22dd3dd4`. `⏎` marks a line break. The asking-site-only prototype and the existing unshared mode agree **on these witnesses**. `x@0` identifies a required parameter and its capture depth. An exported member has no such capture.

| Program | Today | Asking-site only | C | RES-08 |
| --- | --- | --- | --- | --- |
| `F(y) = { A = y + 1 ⏎ public H(k) = Box.R + k ⏎ H(1) }` with `Box = { public R = if(false, F.A, 0) }`; `F.H(1)` | `H` `y@0`; refused at `H` | same | `H` exported; `1` | exported |
| the same with `public H = Box.R`; `F.H` | `H` exported; `0` | `H` `y@0`; refused at `H` | exported; `0` | exported |
| `K = { public M(z) = F.G + z }`, `F(x) = { public G = x + 1 ⏎ public H = K.M(1) ⏎ 0 }` | `H` exported | `H` `x@0` | exported | exported |
| the same with `public H(y) = K.M(1) + y` | `H` `x@0` | `x@0` | exported | exported |
| `H = K.M(1)`; `F.H` (the read is demanded) | refused at `G` inside `K.M` | refused at `H` | refused at `G` | refused at `G` |
| `H = [K.M(1), 7][1]`; `F.H` (the read is never demanded) | `7` | refused at `H` | `7` | `7` |
| `F(x) = { public G = x + 1 ⏎ public W = F.G ⏎ public X = [W, 7][1] ⏎ X }` with `R = F.W` at the root; `F.X` | `W`, `X` exported; `7` | `W`, `X` `x@0`; refused at `X` | `x@0`; refused at `X` | local-only (refused) |
| the same without `R` | `x@0`; refused at `X` | same | same | same |
| a two-library component inside `F` reading `K.M(1)`; `F.R` (`TheResolutionWideGuard_…`) | `R` exported; `7` | `R` `x@0`; refused at `R` | exported; `7` | exported |
| `R = F.G` at the root, or two root readers of `K.M(1)`, with final row `0` | root readers exported; `0` | same | same | exported |
| `H = G + 1` or `H = F.G + 1` inside `F(x)` with `G = x + 1`, output row `H`, final call `F(5)` | `H` requires `x@0`; `7` | same | same | local-only |

Declaring `K` before or after `F`, or nesting the library (`Z = { W = { … } }`), changed no outcome among the orders tried. The order dependence the rule document describes is the order of settlements, which the program's structure fixes. Runs use the public engine entry (`KatLangEngine.Run`).

The third and fourth rows show the key dependence (effect 2), and the fifth and sixth show the latent check. With the library on line 1 as printed, the eager demand reports `LocalOnlyProperty(G)` at line 1, column 21 inside `K.M`, under the calls to `H` and `M`. The lazy selection returns `7`. The asking-site rule alone would move the refusal to `H` and refuse a program that runs today.

## Cost

Settlement frames are deterministic. Times and allocations are single observations of the whole parse on MODA. The harness reports binary memory units.

| Shape | Today | B | C |
| --- | --: | --: | --: |
| Off-chain chain `P{i}.A = P{i-1}.A(1) + 1` over `F.G + x`, D = 100 / 200 / 400 | 10,302 / 40,602 / 161,202 (D² + 3D + 2; 898 ms, 324 MiB at 400) | same | 402 / 802 / 1,602 (4D + 2; 108 ms, 35 MiB) |
| On-chain control over `x + 1` | 396 / 796 / 1,596 (4D − 4) | same | same |
| Branching chain (reads two links below), N = 8 / 12 / 16 / 20 | 600 / 4,354 / 30,178 / 207,272 (692 ms, 317 MiB at 20) | same | 60 / 92 / 124 / 156 (8N − 4) |
| Branching control with terminal `x + 1`, same N | 52 / 84 / 116 / 148 | same | same |
| Branching, N = 22 / 24 (995 / 1,083 bytes of source) | 542,786 frames, 1.7 s, 797 MiB; **refused** with `StaticStructureLimitExceeded` after 896,654 frames and about 1.3 GiB | same | 172 / 188, admitted |
| All-to-all component, an unrelated off-chain read declared first, 4 / 8 / 12 libraries | 831 / 29,091 / 229,287 | 186 / 694 / 1,522 | 186 / 694 / 1,522 |
| The same read declared after the component, or none | 186 / 694 / 1,522; 184 / 692 / 1,520 | same | same |
| The chain inside its owner (`F.G` on every link's chain; clause-family owner) | 2,406 / 2,404 at 400 | same | same |

The default work bound is 16,384 plus 1,024 per admitted node and edge. Every frame is one unit of that bound (`SettlementFrameWork`), and other static operations also consume that budget. At 24 links the baseline reports the static-limit diagnostic. The C prototype completes the same source.

Neither option is free on small programs dense in off-chain reads. Over the 4,000 generated programs described below, today's resolution took 498,259 frames in all.

- B took 662,283 (+33%; more on 2,589 programs, fewer on 54). Its admitted components cost as much as anywhere, and a strict discovery that fails still charges its frames.
- Component equations without any guard took 613,973 (+23%).
- C took 718,117 (+44%; more on 1,952, fewer on 1,230; at most ×3.7, from 154 to 570 frames). C re-enables components and recomputes, per reader, the site-dependent answers that the exact-key share used to hand out.

The 678 programs of the legacy corpus took the same 28,901 frames under C. Every generated program stays far below its work bound under every option.

## Options

**A. Keep the exact-key share and the resolution-wide guard.** Nothing changes. The three effects above stay, and so do the quadratic chain, the exponential branch (with its refusal of small programs) and the component cost after any off-chain lookup.

**B. Isolate the component guard where that preserves today's metadata.** After an off-chain lookup, a component is admitted only when its discovery makes no off-chain lookup itself (as today) and every settlement it reaches answers every site at its level (`AnswersEverySite`: no landing below the key's level). Its solution is used only while no further off-chain lookup happens.

For the all-to-all control, each library member reads only its own argument and other library members whose direct requirement sets are empty. Their recursive equations therefore have the empty least solution. The earlier `OffK.M` read is disconnected, the final row supplies the argument, and every member stays exported with both schedules. This gives a safe instance of guard isolation.

For a general component, a sufficient condition is that every direct term and nested answer used in its equations is identical to the exact walk under the same bound owners and views, and that skipping the walk cannot alter any later site-dependent exact answer. An owner found at or above the common level is the same declaration on every descendant chain. A missing owner, an unqualified name resolved by the asking chain, or a different binding on a later site needs separate justification. A depth comparison alone covers none of those cases. The finite share also matters: on the 8-library control B makes 114 stores against A's 206. A shipping isolation must account for subsequent exact stores at the retention boundary, or restrict reuse to cases where they cannot affect a later reader.

Removing the guard (B0) admits a genuine rejection control. In the two-library example it bypasses the exact answer, publishes the members as local-only, and refuses `F.R` at `R`. B0 changed classifications in both guard witnesses and 447 of 4,000 generated programs, with 57 changed run outcomes. B's three snapshot files matched production byte for byte across all 28,827 inputs, including the runs recorded on clean non-fuzz inputs. B solved 2,584 strict components in the generated programs and 4,305 in the fuzz corpus, where 124 reuse attempts encountered a later off-chain lookup.

B targets metadata compatibility for completed elaborations. Its frame charges move in either direction, so a caller close to a static work limit can see different admission. The chain, branch and RES-08 witnesses still behave as in A.

**C. Check-site settlement (recommended).**
1. The seed of a member that a written path navigates (`AddPublishedCharge`), and the value seed of a head property read through the summary fallback, is settled from `CheckSite(reader site, the member's declaring scope)`. That is the deepest level of the reader's chain that the member's scope shares, exactly as value crossings already use it. This implements rule (a) for paths written in a member's body, and with it RES-08's "a check that can never pass".
2. Record each owner that a lookup failed to find, by declaration identity, and each missing name from a names-only lookup. Both an exact entry and a footprint candidate must satisfy this additional condition: the asking chain lacks every recorded owner and binds none of the recorded names. Since nested check sites move outward, absence on the asking chain also establishes absence on its prefixes. The existing successful-landing, bound-owner and view checks still apply. The prototype's `HoldsFrom` refuses both forms of reuse when the record exceeds `MaxFootprint` (16). An exact key that omits the site cannot recover the missing evidence. Recompute in that case, or use a genuinely site-keyed local result.
3. `SawOffChainLookup` retires with both of its gates. Live settlements keep excluding off-chain settlements, unchanged.

Compared with C's own `Unshared` mode, 28,802 of 28,827 snapshots matched byte for byte. Seven of those matches were static-limit refusals in both modes. The other 25 inputs reached `StaticStructureLimitExceeded` only in the unshared mode (6 component fixtures and 19 fuzz programs). Those inputs yield no comparison of completed metadata. The unshared mode disables the share between settlement walks in one elaboration and uses the same lookup-site code. Agreement tests reuse, while the runnable RES-08 examples test which classification callers should receive.

A refinement that dropped an owner as soon as a member's crossed scope excluded it disagreed with its own unshared mode on three fuzz programs. Another route reached that same key without crossing the scope, and a genuine requirement disappeared. C conservatively retains the owner.

**Reject asking-site admission alone (S1).** It makes the chain and branch linear, but still computes a navigated body's check from the outer reader. Across the generated programs it adds requirements to 4,249 properties in 2,027 programs and refuses 147 programs that run today, including a never-demanded read. It also differs from the existing unshared mode on the erroneous fuzz input `g44_03532`: S1 retains four `z@-1` captures there. The 25 one-sided static-limit refusals are separate. **Recording the miss as a deep landing** would conservatively prevent cross-site reuse of that settlement. It leaves repeated walks on the chain and does not correct the lookup site.

## What changes for callers under C

C changes the classification and capture positions supplied to the existing evaluator. Callers can see a different value, refusal site, or front-end admission at a work limit. The proposal requires no public API addition. Lean receives classified properties as input.

- **Fewer refusals.** A member whose only dependence on an enclosing owner is a check that can never pass becomes exported. Reading it from outside the owner succeeds unless the run demands the impossible read, which is then refused at the member the evaluator checks, as RES-08 shows with `Box.R`. Example: `F.H(1)` above becomes `1`. The census M2 entries for `re-entry-2` and `re-entry-4` should close.
- **More refusals, where a gap answer hid a requirement that can pass.** Such a member becomes local-only wherever it is read. In the witness, reading `F.X` from outside `F` is refused at `X` instead of returning `7`, which is what the same program without the unrelated root read already does.
- **Diagnostics.** A demanded impossible read is still refused at the inner member (`G`). A read of a newly local-only member is refused at that member, positioned at the outer read.
- **Capture positions** identify the lexical activations needed for access. Both the owner depths and the required names are observable in the elaborated tree.
- **Deferred branches.** The provisional contribution and the materialized body must use compatible check sites or materialization can report `DeferredBranchForwardsEnclosingParameter`. Their agreement under C is a production acceptance check, including the slow `DeferredProvisionalParitySweepTests`.
- **Editors** read the same metadata (`SemanticModelTests`).

Corpus effect of the recommended prototype, relative to today (snapshot differential; classifications and runs, with runs only where recorded):

| Corpus | Programs with changed metadata | Properties losing / gaining required names | Run outcomes changed |
| --- | --: | --: | --: |
| Legacy and witness cases (827) | 1 (`H(y) = K.M(1) + y`) | 1 / 0 | 0 |
| Generated off-chain programs (4,000) | 885 | 1,008 / 0 (all LocalOnly → Exported) | 71 refusals → successes, 159 refusals moved |
| Fuzz corpus (24,000, no runs) | 70, all with front-end diagnostics | 75 / 52 (83 individual names removed, 58 added); 32 further properties changed capture positions only | not recorded |

One erroneous fuzz program that today's work bound refuses (`g44_06331`) is admitted with its other diagnostics unchanged. The generator writes no detached reader of a member that can pass, so all its changes are removals. The fuzz corpus shows both directions.

## Static charging, invalidation and cancellation

- **Charging.** Each frame costs one unit on the operation's static ledger. B pays for failed discoveries as well as successful ones. C's admission test scans up to 16 owners or names, potentially walking the asking chain for each. `RecordSettlementFootprintWork` updates an optional observation counter. A production implementation must charge the actual ledger for new traversal work even with observations disabled, account for retained owner/name records in the share's weight, and bound any cache of `CheckSite` results. The prototype omits these new charges. Its frame counts are reproducible; its admission of the 24-link branch must be rechecked with the full charges in place.
- **Invalidation.** Both exact entries and candidates must still pass fact-view version checks. A change to any consulted view requires recomputation. A live summary needs the existing name/revision checks, and an off-chain result remains ineligible for general live reuse. B additionally expires its strict component solution after a subsequent off-chain observation. Eager and deferred attempts have separate shares. A failed or cancelled attempt must publish no reusable partial result.
- **Cancellation.** With a 400 ms source-processing token, the baseline probe cancelled during settlement on the depth-400 chain and the 22-link branch (36,672 and 82,789 frames). C finished before the token fired in those samples (209 and 9 ms). That comparison measures less work. To verify cancellation under C, request it after entering the new lookup or discovery path, assert delivery of the original token, then retry with a fresh attempt. Bound the work between checks during long chain walks as well as at frame boundaries.

## On owner approval of C

1. Implement the approved check site independently of reuse. Check `AddPublishedCharge` and the head-value fallback, and keep the existing consulted-level and transparent-reference rules. To enable sharing, propagate off-chain records through nested seeds and reused partial components, check exact and footprint entries on lookup and store, and enforce the static work and retention limits above before retiring the two global gates.
2. Compare the following independent observations.
   - compare shared and unshared classification, capture depth and diagnostic provenance on completed inputs, and account separately for every admission difference;
   - every changed property is explained by effect 1 or effect 3;
   - exercise the 16-entry limit and overflow, wrong-site exact hits, stale views, strict-component rejection, cancellation and a fresh retry. Check both directions of the caller examples against RES-08.
3. Tests:
   - flip `OffChainExposureDecisionTests` to the decided outcomes;
   - update `ExposureResidualReuseTests.AnOffChainTerminal_KeepsExactKeys_AndItsLatentCheckIsObservable` (4D + 2 frames; the latent check stays) and `ExposureSettlementFootprintTests.ASettlementWithAnOffChainOwner_IsAnsweredForItsExactBoundOwnersOnly`, whose premise changes;
   - rerun the route census and retire each M2 entry only if its independent model and the new classification agree;
   - add a conformance case for RES-08 with a reader inside the owner.
4. Documents: rewrite THE OFF-CHAIN GAP and THE OFF-CHAIN TERMINAL in `evaluator-and-hosting.md`, state point 1 in the Q1–Q3 paragraph of `ownership-and-lookup.md`, and update the exposure row of `SEMANTIC-ALIGNMENT.md` ("Lean update required? No": Lean takes the classification as input, Q-59).
5. On MODA, record the owner decision and the resulting revision in the live Constitution: a dated note, and a RES-08 example with a reader inside the owner (`F.H(1)` is `1`). Also record the decision in the review log and the issue ledger.
6. V3 on the final candidate: the fast .NET phase, `DeferredProvisionalParitySweepTests` from the slow tier, and all seven Lean targets.

If the owner keeps today's metadata, assess B against A's exact answers, including the guard rejection and finite-retention controls. B requires its own proof of the chosen isolation boundary, frame comparison and V3 before landing.

## Verification of this brief and its limits

- **Starting point.** The implementation handoff records a clean start at `22dd3dd49714adcac9cbc50a2dff89bc5953164e` on `main`. Subsequent exposure work since `5d747bb8` includes path parts and bounded seed folding. The live MODA checkout still contains both guard sites and the off-chain witness.
- **Reproduced at that commit.** The brief's frame counts (10,302 / 40,602 / 161,202; 600 / 4,354 / 30,178 / 207,272; 831 / 29,091 / 229,287 against 184 / 692 / 1,520) and the pinned `LocalOnlyProperty`.
- **Prototypes, scratch only.** Built as patches to an export of `dotnet/src/KatLang` outside the checkout, behind environment switches. With the switches off in the guard experiment, its recorded snapshots matched production across 28,827 inputs.
- **Corpora.** The 827-program comparison included the legacy/audit inputs and the chain, branch, component, gap and order fixtures. The later RES-08 and detached-reader witnesses were run separately. There were 4,000 generated off-chain programs with runs and 24,000 fuzz inputs without runs. The comparison helper groups several incomplete outcomes under one label; the underlying C/unshared snapshots identify all 25 one-sided differences as static work-limit diagnostics.
- **Evidence location.** The probe sources, generator, patches and differential logs are saved in the ignored `artifacts/validation/offchain-decision-2026-11-27/` directory.
- **Proof boundary.** The complete source examples distinguish the intended contract from A and S1. The corpus comparisons sample the compatibility of B and the reuse rule of C. They do not prove either result for every program.
- **Executable pins.** `OffChainExposureDecisionTests` pins today's outcomes on these witnesses and names which ones each option flips.

### Reproducing the focused checks

From the repository root, build the affected test project and run the decision, documentation and original latent-check witnesses:

```powershell
$project = 'dotnet/tests/KatLang.Tests/KatLang.Tests.csproj'
dotnet build $project -c Debug
dotnet test $project -c Debug --no-build --filter 'FullyQualifiedName~OffChainExposureDecisionTests|FullyQualifiedName~MaintainedDocumentationConsistencyTests|FullyQualifiedName~AnOffChainTerminal_KeepsExactKeys'
```

The larger measurements used the MODA evidence directory as working directory. For example, `dotnet C:/Temp/ocl/out-base/KatLang.Benchmarks.dll frames dir:cases/chain dir:cases/branch dir:cases/scc` runs the baseline shapes. The same command against `out-proto2` with process environment `OCL_GUARD=safe` selects B, or with `OCL_SITE=2` selects C. These scratch builds, source inputs and raw snapshots are local evidence. The two complete programs and the test sources are part of the checkout.
