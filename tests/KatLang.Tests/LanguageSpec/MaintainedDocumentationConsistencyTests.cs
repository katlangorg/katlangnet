using System.Text.RegularExpressions;

namespace KatLang.Tests.LanguageSpec;

/// <summary>
/// Keeps the maintained descriptions of KatLang telling one story on the rules the
/// September 2026 pre-release documentation sweep found drifting apart. Behavior is pinned
/// by the executable specification; these checks guard only prose that RESTATES it:
/// <list type="bullet">
///   <item>the operator-precedence ladder, restated in five places, keeps the frozen tier
///   order (<c>or</c> &lt; <c>xor</c> &lt; <c>and</c> &lt; prefix <c>not</c> &lt; the ONE
///   comparison tier &lt; <c>+ -</c> &lt; <c>* / div mod</c> &lt; prefix <c>-</c> &lt;
///   <c>^</c>);</item>
///   <item>the user-facing guides state that indexing is zero-based;</item>
///   <item>no current-rule text uses a formulation that is the SHAPE of a superseded rule:
///   a number glossed as a truth value, <c>not</c> placed against two comparison tiers, or
///   <c>exported</c> — an EXPOSURE classification — used where only the PUBLIC visibility of
///   an <c>open</c> member or the DECLARED members of structural navigation are meant
///   (K1-08: selection never depends on exposure).</item>
/// </list>
/// Historical records (the alignment manifest, the dated design notes) narrate superseded
/// rules on purpose and are not scanned; tests are not scanned either, because they quote
/// stale shapes to reject them.
/// </summary>
public class MaintainedDocumentationConsistencyTests
{
    /// <summary>Documents that state the CURRENT language rules.</summary>
    private static readonly string[] CurrentRuleDocuments =
    [
        "AGENTS.md",
        "README.md",
        "tutorial.md",
        "KatLang.ebnf",
        ".github/agents/katlang-generator.agent.md",
        "experimental/prompts/katlang-generator.txt",
        "docs/design/language-rules/README.md",
        "docs/design/language-rules/syntax.md",
        "docs/design/language-rules/sequences-lists-and-calls.md",
        "docs/design/language-rules/ownership-and-lookup.md",
        "docs/design/language-rules/evaluator-and-hosting.md",
        "docs/design/language-rules/editor-semantics.md",
        "src/KatLang/CALLABLES.md",
        "src/KatLang/BINDING-ARCHITECTURE.md",
    ];

    /// <summary>
    /// Formulations that express a superseded rule. Each is narrow on purpose: it matches the
    /// shape the stale rule took, never a topic, so current prose about the same subject is
    /// unaffected.
    /// </summary>
    public static TheoryData<string, string> StaleShapes() => new()
    {
        // Booleans are a value kind with no numeric encoding: `x == y` is `true`, never `1` (true).
        { @"(?<![\w.])`?[01]`?\s*\((?:true|false)\)", "a number glossed as a Boolean truth value" },
        // Equality and ordering share ONE comparison tier; `not` binds below all six.
        { @"(?:comparison and equality|equality and comparison) operators", "two comparison tiers" },
        // Structural dot navigation selects DECLARED members and then checks accessibility.
        { @"exported structural members?", "exposure-filtered structural navigation" },
        // `open` selects PUBLIC members; exposure is checked on the selected member afterwards.
        { @"\bpublic\s*(?:\+|and)?\s*exported\b", "open selection by exposure" },
        { @"\bexported\s+(?:propert(?:y|ies)|members?)\s+for\b", "public visibility called 'exported'" },
        { @"\bexport(?:ed|s)?\s+(?:\w+\s+){0,3}(?:through|via|by)\s+`?open\b", "public visibility called 'exported'" },
        { @"\bproviders?\s+exports?\b", "public visibility called 'exported'" },
        { @"\bexported\s+(?:clause-style\s+)?APIs?\b", "public visibility called 'exported'" },
        // Indexing is zero-based (source line/column coordinates are 1-based, a different thing).
        { @"\b(?:one|1)-based\s+(?:index|indexing|selection)\b", "one-based indexing" },
        // Q-03: implicit lifting follows zero-argument acceptance. A callable that works with no
        // arguments is read by its bare name, and lifting never treats its collector like a
        // required parameter.
        { @"\bunchanged\s+for\s+collecting\s+and\s+fixed\s+parameters\s+alike\b", "lifting unchanged for collecting parameters (before Q-03)" },
        // Q-04: automatic parameter forwarding must not change what an existing name refers to. A
        // forwarded parameter belongs to the call interface only; it never joins the parameters
        // a written name can denote, so "completed" signatures no longer re-own written names.
        { @"\bcomplet(?:e|ed)\s+(?:owner\s+)?(?:signatures?|parameters?)\s+include\s+(?:later\s+)?(?:implicit\s+)?forwarding\s+captures\b", "forwarded parameters owning written names (ownership completion before Q-04)" },
        // Q-05: a repeated name is a compatibility constraint over independently supplied
        // arguments. Every occurrence supplies its own value, so no verdict ever sees a
        // valueless contribution, and no binding pairs one argument's value with another's
        // callable.
        { @"\btwo\s+algorithm-channel\s+bindings\s+only\s+when\s+(?:each|both)\s+carr(?:y|ies)\s+a\s+value\b", "valueless repeated contributions accepted beside values (before Q-05)" },
        { @"\balgorithm-only\s+repeat(?:s|ed\s+names?)?\b", "an algorithm-only repeated-name verdict (before Q-05)" },
        { @"P\(5,\s*Inc\)`?\s+binds\b", "a value spliced with another argument's callable (before Q-05)" },
        // Formula lifting is by binding name, regardless of how many times that name occurs in a
        // callee's parameter patterns (September 29 2026, reversing the Q-72 refusal of the same
        // day; narrowed to formulas by the alias and bare-forwarding rules): a callee that
        // repeats a name lifts like any callee — one caller binding per name, supplied to every
        // occurrence — and no front-end diagnostic refuses it.
        { @"\bRepeatedParameterNotForwardable\b", "the removed repeated-name forwarding refusal diagnostic (Q-72, reversed)" },
        { @"\bcannot\s+be\s+forwarded\s+implicitly\b", "the repeated-name forwarding refusal (Q-72, reversed)" },
        { @"\bno\s+implicit\s+forwarding\s+into\s+a\s+repeated-name\s+callee\b", "the repeated-name forwarding refusal (Q-72, reversed)" },
        { @"\bnever\s+(?:takes?|participates?)\s+(?:part\s+)?in\s+implicit\s+(?:parameter\s+)?(?:forwarding|lifting)\b", "a callee excluded from implicit forwarding (Q-72, reversed)" },
        // PV-05 / PV-19 / PV-20: builtin call assembly respects argument roles. A callback slot is
        // never value-evaluated merely because it was supplied, so no value outcome can fall
        // through to it; `reduce`'s `initial` is an ordinary value control.
        { @"\bcallback\s+fall-?through\b", "a builtin callback slot's value fall-through (before PV-19)" },
        { @"\bcallback\s+slot'?s\s+eager\b", "an eager value attempt in a builtin callback slot (before PV-19)" },
        { @"`?initial`?\s+shares\s+the\s+algorithm\s+metadata\s+kind", "reduce's initial as an algorithm-kind slot (before PV-05)" },
        // PV-11: an open target is an open form ALL the way down — the head of a dotted path is
        // validated like a bare target — so no parser check "passes" a target by its outer node.
        { @"\bpass(?:es|ing)\s+(?:that|the)\s+(?:parser|outer(?:[- ]dot)?[- ]form)\s+check\b", "an open target validated by its outer node only (before PV-11)" },
        // PV-24: clause-family opens are branch-owned; a family owns no opens of its own.
        { @"\bopens\s+list\s+is\s+taken\s+from\s+the\s+first\s+branch", "a clause family owning its first branch's opens (before PV-24)" },
        // Structural patterns select the value kind they destructure (September 29 2026): a
        // sequence pattern opens sequence values only, a list pattern list values only, a scalar
        // is never a one-item structure, and a one-item sequence pattern is invalid source.
        { @"(?<!\bno\s{1,3})\bscalar\s+one-item\s+fallback\b", "a structural pattern's scalar one-item fallback (before the structural kind law)" },
        { @"\bsequenceValuePatternItems\b", "the kind-blind structural pattern opener (before the structural kind law)" },
        { @"\bpatternSequenceValueMembers\b", "the family matcher's scalar arm (before the structural kind law)" },
        { @"\bsingleton\s+sequence-value\s+(?:fallback|normalization)\b", "a singleton sequence pattern binding a whole value (before the singleton rule)" },
        { @"\blist\s+patterns\s+are\s+deferred\b", "clause families without list patterns (before the structural kind law)" },
        { @"\bsequence(?:-value)?\s+patterns?\s+(?:also\s+)?opens?\s+(?:a\s+|the\s+)?(?:list|sequence\s+or\s+(?:a\s+)?list)\b", "a sequence pattern opening a list (before the structural kind law)" },
        // The alias and bare-forwarding rules (FWD-02, September 29–30 2026): a lone bare row is an
        // CALLABLE ALIAS of the callable it names or BARE FORWARDING — each parameter supplied by name
        // from an existing compatible binding, never completed by the callee's binder names into a
        // new signature. Formula lifting keeps forwarding by binding name.
        { @"`?\b(?:Some|Alias|A)\s*=\s*P`?\s+(?:is|elaborates\s+to|becomes)\s+`?(?:Some|Alias|A)\(x\)\s*=\s*P\(x,\s*x\)", "an alias of a repeated-name callee deduplicated by binding name (before the alias rule)" },
        { @"`?\bG\(x\)\s*=\s*Single`?\s+(?:is|elaborates\s+to|becomes)\s+`?G\(x\)\s*=\s*Single\(\[x\]\)", "a lone row completed by the callee's binder name (before the alias and bare-forwarding rules)" },
        { @"\bAlias\s*=\s*Cnt`?\s+(?:is|elaborates\s+to|becomes)\s+a\s+zero-parameter\s+property", "a zero-parameter alias of a collecting-only callable (Q-03's alias clause, before the alias rule)" },
        // The unified formula-lifting law (September 30 2026): a formula lifts a reference whenever
        // its immediate consumer uses it as a VALUE and the callable it resolves to — whatever its
        // category and route — has a lifting signature; builtin value slots, capture elements and
        // nested argument expressions are value positions, and clause families lift when their
        // clauses name them.
        { @"\bnever\s+implicitly\s+forwarded\b", "opened callables excluded from formula lifting (before the unified law)" },
        { @"\bregistry-strict\s+Math\s+positions\s+lift\b", "only Math arguments lifting among call arguments (before the unified law)" },
        { @"\bProcessValueDemandingArgumentBundle\b", "the removed Math-only value-context lifting helper (before the unified law)" },
        { @"\bclause\s+famil(?:y|ies)\s+(?:is\s+|are\s+)?(?:still\s+)?never\s+lifted\b", "clause families excluded from formula lifting (before the unified law)" },
        { @"\bcapture\s+rows?\s+(?:intentionally\s+)?(?:do|does)\s+not\s+lift\b", "capture elements excluded from formula lifting (before the unified law)" },
        { @"\blifting\s+a\s+bare\s+Math\s+function\s+(?:stays|is)\s+route-based\b", "route-based Math lifting (before the unified law)" },
        // Callable aliases are binding indirection (October 1 2026): `A = F` is a second name for F's
        // callable — no wrapper, no inherited signature, no rebuilt call — for EVERY callable that
        // declares parameterized structure, whatever route reached it; a zero-parameter target is read.
        { @"\bexact\s+alias(?:es)?\b", "the exact-alias wrapper (before callable aliases as binding indirection)" },
        { @"\bInheritsCalleeSignature\b", "the alias's inherited-signature flag (before binding indirection)" },
        { @"\baliasesLoneBareReference\b|\bsourceCall\b", "the Lean wrapper-alias specification (before binding indirection)" },
        { @"\balias(?:es)?\s+inherits?\s+(?:the\s+|its\s+)?(?:callee'?s|target'?s)\s+(?:patterns|signature|parameters)\b", "an alias inheriting its callee's signature (before binding indirection)" },
        { @"\bnot\s+alias\s+or\s+forwarding\s+targets\b", "route-based lone-row alias eligibility (before binding indirection)" },
        { @"\bC\s*=\s*count`?\s+stays\s+(?:a\s+zero-parameter|an\s+ordinary)\s+property\b", "a builtin's lone row as a zero-parameter property (before binding indirection)" },
        // X-23 (October 2026): a loop-state mismatch whose step contributes no parameter label is
        // reported by that binding fact alone. Its one payload cannot tell a zero-parameter
        // algorithm from a clause family, a builtin, an alias of either or a value, so no text
        // explains it as a step that has no parameters.
        { @"\bbecause\s+the\s+step\s+has\s+no\s+parameters\b", "the false loop-step explanation (before X-23)" },
        // Q-09 (October 4 2026). Q-09b: limits observe a run; they never choose how it runs, so no
        // text says a configured budget selects, disables or forces an evaluation strategy.
        // Q-09a: host-stack headroom is not semantic — the async twin can stop shallower OR deeper
        // than the synchronous evaluator — and no depth limit is calibrated against the host stack
        // (X-34). `LimitDocumentationContractTests` pins the positive statements in the shipped
        // XML documentation.
        { @"\b(?:budgets?|limits?)\s+(?:\w+\s+){0,4}(?:selects?|disables?|forces?)\s+(?:the\s+)?(?:generic|loop\s+planning|(?:sequence[- ]pipeline\s+)?fusion|optimi[sz])", "a configured limit selecting an evaluation strategy (before Q-09b)" },
        { @"\bcan\s+change\s+which\s+internal\s+evaluation\s+strategy\s+runs\b", "a configured limit selecting an evaluation strategy (before Q-09b)" },
        { @"\balways\s+(?:\w+\s+){0,6}(?:earlier|shallower)\b", "a host-stack backstop that always fires earlier on one route (before Q-09a)" },
        { @"\bmeasured\s+margin\b|\b\d+(?:\.\d+)?x\s+\((?:Debug|Release)\)", "a portable calibrated stack-safety margin (before X-34)" },
        { @"calibrat\w*[^.;]{0,60}\b(?:depth\s+ceiling|depth\s+limit|depth\s+envelope|MaxSupportedDepth|MaxDepth)\b", "a depth limit calibrated against the host stack (before X-34)" },
        { @"\b(?:MaxSupportedDepth|depth\s+ceiling|depth\s+limit|depth\s+envelope)\b[^.;]{0,60}\bcalibrat", "a depth limit calibrated against the host stack (before X-34)" },
        // Q-24 (October 4 2026): a loop step's parameter patterns bind the incoming state only; its
        // row supply is the next state and NO pattern category repacks a spread row. The packing
        // and the machinery that existed only to compute its flag are deleted, never to return.
        { @"\bpack(?:s|ed|ing)?\s+(?:a\s+|its\s+|the\s+)?top-level\s+(?:output\s+)?spread\b", "pattern-triggered loop-output packing (before Q-24)" },
        { @"\bpacked[\s-]+(?:next-state\s+)?slot\b", "pattern-triggered loop-output packing (before Q-24)" },
        { @"\b(?:requiresPatternBinding|hasRepeatedParameterNames|[Pp]reserveSequenceSpreadExpressionBoundaries|ShouldPreserveLoopStepSequenceSpreadExpressionBoundaries|SelectGenericLoopStepBinding|GenericLoopStepBindingShape|GenericLoopStepBindingSelection|FlatCollectingBindingLayout|TryGetFlatCollectingBindingLayout)\b", "the retired loop-output packing machinery (before Q-24)" },
        // Q-26 (October 4 2026): a completed `while`/`repeat` is an ordinary value boundary — ONE
        // value with count valueCount at every receiver — so no text lists loop results among the
        // non-boundaries, lets a loop row emit its slots, or keeps SUP-01's nested-loop exception.
        { @"\bNOT\s+value\s+boundaries\b[^.]{0,200}\bwhile`?/`?repeat\b", "loop results listed as not a value boundary (before Q-26)" },
        { @"\bmulti-slot\s+loop\s+(?:result|state)\s+(?:may\s+)?emits?\s+(?:several|its|k)\b", "a loop result emitting its slots as rows (before Q-26)" },
        { @"\bwhich\s+(?:intentionally\s+)?preserve\s+multi-slot\s+loop\s+state\b", "a loop result keeping its slot count (before Q-26)" },
        { @"\bsole\s+exception:\s+a\s+nested\s+loop\s+row\b", "SUP-01's nested-loop step-row exception (before Q-26)" },
        { @"\bcontributes\s+its\s+k\s+(?:state\s+)?slots\b", "a nested loop row contributing its slots (before Q-26)" },
        // Q-23 (October 2026): a loop step is an ordinary callable invoked over the current state
        // supply. Any callable is eligible — a clause family dispatches its clauses, a builtin runs
        // through its argument roles — so no text restricts steps by category or recommends a
        // wrapper to make a family or builtin a step.
        { @"\b(?:clause[- ]famil(?:y|ies)|builtins?)\s+(?:is|are)\s+(?:not|never)\s+(?:a\s+|an\s+)?(?:valid\s+|eligible\s+)?(?:loop\s+)?steps?\b", "a loop step restricted by callable category (before Q-23)" },
        { @"\bwrap\w*\s+(?:a\s+|the\s+)?(?:clause[- ]family|family|builtin)\s+(?:\w+\s+){0,4}as\s+a\s+(?:loop\s+|while\s+|repeat\s+)?step\b", "a wrapper required to use a family or builtin as a loop step (before Q-23)" },
        { @"\b(?:only|just)\s+(?:a\s+)?user(?:-defined)?\s+(?:algorithms?|callables?)\s+(?:can|may)\s+be\s+(?:a\s+)?(?:loop\s+)?steps?\b", "a loop step restricted to user algorithms (before Q-23)" },
        // Q-27 + Q-06 (October 5 2026): an evaluation error names the first contract the operation
        // cannot satisfy. `first`/`last` ARE selections, so the selection laws are total (errors
        // included) and an empty `first` is BadIndex, never an arity error; a value in an invoking
        // slot is NotAnAlgorithm, never an arity error against an invented zero-parameter thunk.
        { @"wherever\s+(?:the\s+selection\s+is\s+)?valid", "the selection laws restricted to valid selections (before Q-27)" },
        { @"first\(\(\)\)`?\s+(?:is|gives|reports)\s+(?:an?\s+)?`?(?:arity|ArityMismatch|BadArity)", "an empty `first` as an arity error (before Q-27)" },
        { @"arity\s+error\s+on\s+the\s+value\s+thunk", "a value callback reported as the arity of an invented thunk (before Q-06)" },
        // Q-16 G-O (October 7 2026): Grace is an owner-local ordering weight that requires an OWN
        // inferred parameter — eligibility, never movement (a saturated marker is valid) — and a
        // clause branch is closed at its OWN level only, so an algorithm nested in a branch keeps its
        // Grace. No current text demands that a marker move, quotes the retired messages, or bans
        // Grace from everything lexically inside a branch body.
        { @"\bGRACE\s+MUST\s+BE\s+EFFECTIVE\b", "Grace validity worded as effectiveness (F10's wording before Q-16 E)" },
        { @"\bGrace\s+has\s+no\s+effect\s+on\b", "the retired ineffective-Grace message (before Q-16)" },
        { @"\bmarker\s+that\s+could\s+reorder\s+nothing\s+is\s+an?\s+error\b", "every non-moving Grace marker as an error (before Q-16 E)" },
        { @"\bGrace\s+is\s+not\s+allowed\s+in\s+(?:conditional\s+)?(?:clause\s+)?branch\s+bod(?:y|ies)\b", "the lexical branch-body Grace ban (before Q-16 O)" },
        { @"\bGrace\b[^.]{0,20}\b(?:not\s+permitted|forbidden|not\s+allowed)\s+in\s+(?:both\s+)?(?:branch\s+)?patterns\s+(?:or|and)\s+(?:branch\s+)?bodies\b", "Grace banned from whole branch bodies (before Q-16 O)" },
        { @"\bno\s+Grace\s+in\s+(?:conditional\s+)?branch\s+bod(?:y|ies)\b", "Grace banned from whole branch bodies (before Q-16 O)" },
        // X-49 (October 8 2026): the multi-marker Grace ORDER is decided — postfix movers first, from
        // the last-occurring, then prefix movers from the first-occurring, residual weights kept —
        // and weights are exact unbounded integers. No current text calls the order an undecided
        // candidate, names the retired position-cursor procedure, or describes clamped weights.
        { @"\bApplyGraceReordering\b", "the retired position-cursor Grace ordering procedure (before X-49)" },
        { @"\bcandidate\s+X-49\b", "the multi-marker Grace order as an undecided candidate (before X-49)" },
        { @"\bmulti-marker\s+(?:order|iteration)\b[^.]{0,60}\b(?:is\s+unchanged|is\s+the\s+implementation's|does\s+not\s+fully\s+determine)", "the multi-marker Grace order left to the implementation (before X-49)" },
        { @"\bGraceWeightEffect\b|\bint-saturating\s+(?:grace\s+)?(?:weights?|additions?)\b", "int-saturating Grace weight arithmetic (before X-49)" },
        // X-49 F1: equal weights preserve relative order. Translation of a contiguous run as a
        // unit requires every outside weight to be zero; other movers can split the run.
        { @"\bneighbours\s+marked\s+the\s+same\s+way\s+move\s+together\b", "the unconditional same-marked-neighbours group claim (X-49 F1)" },
        { @"\bequally\s+marked\s+runs\s+move\s+as\s+a\s+unit\b", "the unconditional equally-marked-run group claim (X-49 F1)" },
        { @"\badjacent\s+names\s+with\s+one\s+common\s+weight\s+move\s+as\s+a\s+unit\b", "the unconditional adjacent-equal-weight group claim (X-49 F1)" },
    };

    [Theory]
    [MemberData(nameof(StaleShapes))]
    public void CurrentRuleText_NeverUsesTheShapeOfASupersededRule(string pattern, string supersededRule)
    {
        var regex = new Regex(pattern, RegexOptions.IgnoreCase | RegexOptions.CultureInvariant);
        var hits = new List<string>();
        var scanned = 0;
        foreach (var (relativePath, text) in CurrentRuleTexts())
        {
            scanned++;
            var lines = text.ReplaceLineEndings("\n").Split('\n');
            for (var index = 0; index < lines.Length; index++)
            {
                if (regex.Match(lines[index]) is { Success: true } match)
                    hits.Add($"{relativePath}:{index + 1}: '{match.Value}'");
            }
        }

        // The source and Lean scan is not allowed to silently shrink to nothing.
        Assert.True(scanned > CurrentRuleDocuments.Length + 100, $"Only {scanned} files were scanned.");
        Assert.True(
            hits.Count == 0,
            $"Current-rule text uses the shape of a superseded rule ({supersededRule}):\n" + string.Join("\n", hits));
    }

    /// <summary>
    /// Every restatement of the operator-precedence ladder lists the tiers in the frozen
    /// order and names every tier. Tokens are compared by TIER, so a tier's internal spelling
    /// order and the presentation (a one-line ladder, a numbered list, the tutorial's
    /// reference table read bottom-up) are free.
    /// </summary>
    [Theory]
    [InlineData("AGENTS.md")]
    [InlineData("docs/design/language-rules/syntax.md")]
    [InlineData(".github/agents/katlang-generator.agent.md")]
    [InlineData("experimental/prompts/katlang-generator.txt")]
    [InlineData("tutorial.md")]
    public void PrecedenceLadder_ListsTheFrozenTiersInOrder(string relativePath)
    {
        var text = File.ReadAllText(Path.Combine(RepoRoot.Find(), relativePath)).ReplaceLineEndings("\n");
        var tokens = relativePath switch
        {
            "experimental/prompts/katlang-generator.txt" => NumberedLadderTokens(text),
            "tutorial.md" => ReferenceTableLadderTokens(text),
            _ => InlineLadderTokens(text),
        };

        var tier = 0;
        var tiersSeen = new HashSet<int>();
        foreach (var token in tokens)
        {
            // The smallest tier at or above the current one that spells the token: `-` is
            // additive right after `+` and prefix minus after the multiplicative tier.
            var next = -1;
            for (var candidate = tier; candidate < PrecedenceTiers.Length && next < 0; candidate++)
            {
                if (PrecedenceTiers[candidate].Contains(token))
                    next = candidate;
            }

            Assert.True(next >= 0, $"{relativePath}: `{token}` appears out of precedence order in the ladder [{string.Join(" ", tokens)}].");
            tier = next;
            tiersSeen.Add(tier);
        }

        Assert.True(
            tiersSeen.Count == PrecedenceTiers.Length,
            $"{relativePath}: the ladder [{string.Join(" ", tokens)}] does not name every precedence tier.");
    }

    /// <summary>
    /// The user-facing guides state the index base explicitly: selection counts from zero.
    /// </summary>
    [Theory]
    [InlineData("tutorial.md")]
    [InlineData(".github/agents/katlang-generator.agent.md")]
    [InlineData("experimental/prompts/katlang-generator.txt")]
    public void UserFacingGuide_StatesZeroBasedIndexing(string relativePath)
    {
        var text = File.ReadAllText(Path.Combine(RepoRoot.Find(), relativePath));
        Assert.Contains("zero-based", text, StringComparison.OrdinalIgnoreCase);
    }

    [Theory]
    [InlineData("docs/design/language-rules/ownership-and-lookup.md")]
    [InlineData("tutorial.md")]
    [InlineData(".github/agents/katlang-generator.agent.md")]
    [InlineData("experimental/prompts/katlang-generator.txt")]
    public void GraceGroupTranslation_StatesItsZeroWeightCondition_AndTheSplitCounterexample(string relativePath)
    {
        var text = File.ReadAllText(Path.Combine(RepoRoot.Find(), relativePath));
        Assert.Contains("Equal accumulated weights preserve their original relative order.", text);
        Assert.Contains("A contiguous equal-weight run moves as a unit when every parameter outside that run has zero weight.", text);
        Assert.Contains("Other moving parameters can split the run while preserving its relative order.", text);
        // The claims above are observed by GraceMovementLawTests and TutorialSemanticContractTests;
        // each maintained restatement must also show the witness that prevents a contiguity reading.
        Assert.Contains("K = a~ * 1000 + b~ * 100 + ~c * 10 + ~d", text);
        Assert.Contains("(c, a, d, b)", text);
        Assert.Contains("2413", text);
    }

    /// <summary>Loosest first. Prefix <c>-</c> is its own tier, above the multiplicative one.</summary>
    private static readonly string[][] PrecedenceTiers =
    [
        ["or"],
        ["xor"],
        ["and"],
        ["not"],
        ["<", ">", "<=", ">=", "==", "!="],
        ["+", "-"],
        ["*", "/", "div", "mod"],
        ["-"],
        ["^"],
    ];

    private static readonly HashSet<string> LadderOperators =
        [.. PrecedenceTiers.SelectMany(static tier => tier)];

    private static readonly Regex BacktickedToken = new("`([^`]+)`", RegexOptions.CultureInvariant);

    /// <summary>A one-line ladder <c>`or` &lt; `xor` &lt; … &lt; `^`</c>: from its first rung through `^`.</summary>
    private static List<string> InlineLadderTokens(string text)
    {
        var start = text.IndexOf("`or` < `xor`", StringComparison.Ordinal);
        Assert.True(start >= 0, "No one-line precedence ladder starting with `or` < `xor` was found.");
        var end = text.IndexOf("`^`", start, StringComparison.Ordinal);
        Assert.True(end > start, "The one-line precedence ladder does not reach `^`.");
        return OperatorTokens(text[start..(end + "`^`".Length)]);
    }

    /// <summary>The numbered list under "Operator precedence, lowest to highest:".</summary>
    private static List<string> NumberedLadderTokens(string text)
    {
        var header = text.IndexOf("Operator precedence, lowest to highest:\n", StringComparison.Ordinal);
        Assert.True(header >= 0, "No numbered precedence ladder was found.");
        var rungs = text[header..]
            .Split('\n')
            .Skip(1)
            .TakeWhile(static line => Regex.IsMatch(line, @"^\d+\. "));
        return OperatorTokens(string.Join("\n", rungs));
    }

    /// <summary>The reference table's operator rows from the Highest row to the Lowest row, read bottom-up.</summary>
    private static List<string> ReferenceTableLadderTokens(string text)
    {
        var header = text.IndexOf("| Operator | Description | Precedence |", StringComparison.Ordinal);
        Assert.True(header >= 0, "No operator reference table was found.");
        var rows = new List<string>();
        foreach (var line in text[header..].Split('\n').Skip(2))
        {
            Assert.StartsWith("|", line);
            rows.Add(line.Split('|')[1]);
            if (line.TrimEnd().EndsWith("| Lowest |", StringComparison.Ordinal))
                break;
        }

        rows.Reverse();
        return OperatorTokens(string.Join("\n", rows));
    }

    private static List<string> OperatorTokens(string ladder)
        => BacktickedToken.Matches(ladder)
            .Select(static match => match.Groups[1].Value)
            .Where(LadderOperators.Contains)
            .ToList();

    private static IEnumerable<(string RelativePath, string Text)> CurrentRuleTexts()
    {
        var root = RepoRoot.Find();
        foreach (var relativePath in CurrentRuleDocuments)
            yield return (relativePath, File.ReadAllText(Path.Combine(root, relativePath)));

        // Source comments and Lean doc comments state the same laws. Build output and
        // package caches (bin, obj, .lake) are not source.
        foreach (var (directory, pattern) in new[] { ("src/KatLang", "*.cs"), ("lean", "*.lean") })
        {
            foreach (var path in Directory.EnumerateFiles(Path.Combine(root, directory), pattern, SearchOption.AllDirectories))
            {
                var relativePath = Path.GetRelativePath(root, path).Replace('\\', '/');
                if (relativePath.Split('/').Any(static segment => segment is "bin" or "obj" || segment.StartsWith('.')))
                    continue;

                yield return (relativePath, File.ReadAllText(path));
            }
        }
    }
}
