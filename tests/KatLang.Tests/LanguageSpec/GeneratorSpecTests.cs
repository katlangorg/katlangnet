using System.Text;
using System.Text.RegularExpressions;

namespace KatLang.Tests.LanguageSpec;

/// <summary>
/// Keeps the katlang-generator prompt files in sync with the canonical
/// specification: a marker-delimited verified-examples block is generated
/// deterministically from the corpus cases flagged
/// <see cref="SpecCase.IncludeInGeneratorPrompt"/> and embedded in BOTH prompt
/// files, so the two prompts can no longer drift apart on those examples and
/// every embedded expectation is engine- and Lean-verified through the
/// corpus. A failure means the block is stale — regenerate with:
///   $env:KATLANG_REGENERATE_LANGUAGE_SPEC = "1"
///   dotnet test .\KatLang.slnx --filter LanguageSpecArtifacts
/// (This class shares the LanguageSpecArtifacts regeneration filter; the
/// regenerating run writes both files and then fails by design — see
/// <see cref="ArtifactRegeneration"/>.)
/// </summary>
public class LanguageSpecArtifactsGeneratorPromptTests
{
    private const string BeginMarker = "=== BEGIN GENERATED: katlang-spec-examples (DO NOT EDIT BY HAND) ===";
    private const string EndMarker = "=== END GENERATED: katlang-spec-examples ===";

    private static readonly string[] PromptFiles =
    [
        ".github/agents/katlang-generator.agent.md",
        "experimental/prompts/katlang-generator.txt",
    ];

    public static TheoryData<string> PromptFilePaths()
    {
        var data = new TheoryData<string>();
        foreach (var file in PromptFiles)
            data.Add(file);
        return data;
    }

    [Theory]
    [MemberData(nameof(PromptFilePaths))]
    public void PromptFile_HandwrittenResultClaimsExecute(string relativePath)
    {
        var text = File.ReadAllText(Path.Combine(RepoRoot.Find(), relativePath));
        var handwritten = text[..text.IndexOf(BeginMarker, StringComparison.Ordinal)];
        // Reuse the tutorial grammar and execution assertions, never a second example parser.
        var claims = TutorialCorpus.Parse(handwritten).Where(e => e.HasResultClaim).ToArray();
        Assert.Equal(10, claims.Length);
        Assert.All(claims, e => Assert.Null(e.SkipReason));
        var required = new[] { "Countdown(0) = 0, false", "Step(x) = x + 1",
            "Step((*history, previous)) = (history*, previous + 1)",
            "Step(first, *middle, last) = first + 1, middle*, last + 1", "Outer(limit) = {",
            "AddToState(item, (total, itemCount)) = (total + item, itemCount + 1)",
            "Append(item, (*history)) = (history*, item)", "ListAppend(item, [*history]) = [history*, item]",
            "Many(*values) = values.count" };
        foreach (var first in required) Assert.Single(claims, e => e.FirstSourceRow == first);
        Assert.Single(claims, e => e.FirstSourceRow == (relativePath.EndsWith(".md", StringComparison.Ordinal)
            ? "Order = {" : "Swap((a, b)) = (b, a)"));
        foreach (var claim in claims) TutorialResultSweepTests.VerifyExample(claim);
        Assert.DoesNotContain("`Many(())` is `[()]`", handwritten, StringComparison.Ordinal);
        Assert.DoesNotContain("`:index`", handwritten, StringComparison.Ordinal);
        Assert.DoesNotMatch(@"`:[0-9]+`", handwritten);
    }

    private static readonly Regex AnnotatedExampleRow = new(@"^[ ]{2,}[^#\s].*?\s+#\s.+$");

    /// <summary>
    /// The prompts' indented examples annotate rows with <c># result</c> comments, a convention
    /// the tutorial fence grammar does not read. Every such row outside a fence is classified here
    /// by its exact trimmed text: it EXECUTES (a program evaluating the row in its example's
    /// context, with the annotated display or error code) or carries an explicit exemption. An
    /// unclassified row or a stale entry fails the census, so editing an annotation can never
    /// silently leave it unverified. The annotation text stays in the prompt; the expected value
    /// here is the annotation's claim, anchored by the verbatim row.
    /// </summary>
    [Theory]
    [MemberData(nameof(PromptFilePaths))]
    public void PromptFile_AnnotatedExampleRowsExecuteOrAreExempt(string relativePath)
    {
        var text = File.ReadAllText(Path.Combine(RepoRoot.Find(), relativePath)).ReplaceLineEndings("\n");
        var found = new SortedSet<string>(StringComparer.Ordinal);
        var inFence = false;
        foreach (var line in text[..text.IndexOf(BeginMarker, StringComparison.Ordinal)].Split('\n'))
        {
            if (line.StartsWith("```", StringComparison.Ordinal))
                inFence = !inFence;
            else if (!inFence && AnnotatedExampleRow.IsMatch(line))
                found.Add(line.Trim());
        }

        var rows = AnnotatedRows[Path.GetFileName(relativePath)];
        Assert.Equal(found, rows.Select(r => r.Row).Order(StringComparer.Ordinal));
        foreach (var row in rows.Where(r => r.Program is not null))
        {
            var run = KatLangEngine.Run(row.Program!);
            var display = run.ToDisplayString().ReplaceLineEndings("\n");
            var context = $"{relativePath}: `{row.Row}`\nProgram:\n{row.Program}\nActual:\n{display}";
            if (row.Error is not { } code)
            {
                Assert.True(run is RunResult.Success && display == row.Display, context);
                continue;
            }

            var errors = run switch
            {
                RunResult.ParseFailure parse when row.FrontEnd => parse.Errors,
                RunResult.EvalFailure eval when !row.FrontEnd => eval.Errors,
                _ => null,
            };
            Assert.True(errors is not null && errors.Count == 1 && errors[0].Code == code, context);
        }
    }

    private sealed record AnnotatedRow(
        string Row, string? Program, string? Display, KatLangErrorCode? Error, bool FrontEnd, string? Exemption);

    private static AnnotatedRow Shows(string row, string program, string display) => new(row, program, display, null, false, null);
    private static AnnotatedRow Fails(string row, string program, KatLangErrorCode code) => new(row, program, null, code, false, null);
    private static AnnotatedRow Rejects(string row, string program, KatLangErrorCode code) => new(row, program, null, code, true, null);
    private static AnnotatedRow Exempt(string row, string reason) => new(row, null, null, null, false, reason);

    private const string NetworkLoad = "network module load: needs a host downloader";
    private const string RejectedLoad = "rejected load form: module loading is host configuration";
    private const string AmbiguousOpenProgram = "open A, B\nA = { public X = 1 }\nB = { public X = 2 }\nX";
    private const string OpenedPiProgram = "open Lib\nLib = {\n    public Pi = 3\n}\nPi";
    private const string EqualFamilyProgram = "Equal(x, x) = 1\nEqual(x, y) = 0\nEqual(2, 2), Equal(2, 3)";
    private const string DuplicateBranchProgram = "F(x) = 1\nF(y) = 2\nF(5)";
    private const string EmptyValues = "A = ()\nB = {}\nIsEven = x mod 2 == 0\n";
    private const string Boundaries = "A = 1, 2\nF(*x) = x\nG(first, *rest) = first, rest\n";
    private const string Slots = "Pair = 10, 20\nAdd = x + y\nTail = 2, 3\nUse = a + b + c\n";
    private const string OpenPair = "\nA = { public X = 1 }\nB = { public Y = 2 }\n";
    private const string Selections = "Values = 10, 20, 30\nPairs = (1, 2), (3, 4)\nRows = [[1, 2], [3, 4]]\n";
    private const string Collections = "Values = 1, 2, 3\n";
    private const string Scale = "Arg = 1, 2, 3\nScale(*values, factor) = values.map{n * factor}\n";
    private const string BackBound = "Values = 10, 20\nSum(*values, last) = values.sum + last\n";

    private static readonly IReadOnlyDictionary<string, AnnotatedRow[]> AnnotatedRows = new Dictionary<string, AnnotatedRow[]>
    {
        ["katlang-generator.agent.md"] =
        [
            Rejects("X                  # error: 'X' is ambiguous: 2 different opened algorithms provide it (A, B)", AmbiguousOpenProgram, KatLangErrorCode.AmbiguousOpen),
            Shows("Pi                  # 3", OpenedPiProgram, "3"),
            Exempt("Lib = load('https://katlang.org/lib.kat')      # property definition", NetworkLoad),
            Exempt("open load('https://katlang.org/lib.kat')       # open list", NetworkLoad),
            Exempt("open 'https://katlang.org/lib.kat'             # shorthand for open load(...)", NetworkLoad),
            Exempt("Lib = load(Url)                                # invalid: URL must be a literal, not a variable", RejectedLoad),
            Exempt("load('https://katlang.org/lib.kat')            # invalid: load is not allowed as runtime output", RejectedLoad),
            Exempt("Lib = load(\"https://katlang.org/{name}.kat\")   # invalid: a URL is fixed text, never interpolated", RejectedLoad),
            Rejects("F(y) = 2             # invalid: same pattern shape as F(x) (duplicate branch)", DuplicateBranchProgram, KatLangErrorCode.DuplicateBranchPattern),
            Shows("Equal(x, x) = 1      # repeated-binder equality: matches only when both arguments are equal", EqualFamilyProgram, "1\n0"),
            Shows("Equal(x, y) = 0      # valid: distinct from the (x, x) equality constraint", EqualFamilyProgram, "1\n0"),
        ],
        ["katlang-generator.txt"] =
        [
            Shows("A                    # ()", EmptyValues + "A", "()"),
            Shows("A.count              # 0", EmptyValues + "A.count", "0"),
            Shows("() == ()             # true", "() == ()", "true"),
            Shows("() == (())           # true", "() == (())", "true"),
            Shows("(()).count           # 0", "(()).count", "0"),
            Shows("count((()))          # 0", "count((()))", "0"),
            Fails("B.count              # error: no defined output", EmptyValues + "B.count", KatLangErrorCode.MissingOutput),
            Fails("B == ()              # error: no defined output", EmptyValues + "B == ()", KatLangErrorCode.MissingOutput),
            Shows("filter((1, 3, 5), IsEven) == ()       # false: filter returns the empty LIST [], and [] != ()", EmptyValues + "filter((1, 3, 5), IsEven) == ()", "false"),
            Shows("filter((1, 3, 5), IsEven) == []       # true", EmptyValues + "filter((1, 3, 5), IsEven) == []", "true"),
            Shows("filter((1, 3, 5), IsEven).count == 0  # true: test collection-builtin emptiness with count(...) == 0 or == [], never == ()", EmptyValues + "filter((1, 3, 5), IsEven).count == 0", "true"),
            Shows("F(A)      # collects A as one supplied argument; displays [(1, 2)]", Boundaries + "F(A)", "[(1, 2)]"),
            Shows("F(A*)     # explicitly opens A first; displays [1, 2]", Boundaries + "F(A*)", "[1, 2]"),
            Shows("G(A)      # first = (1, 2), rest = []   (the call does not open A)", Boundaries + "G(A)", "((1, 2), [])"),
            Shows("G(A*)     # first = 1, rest = [2]       (the spread star opens A first)", Boundaries + "G(A*)", "(1, [2])"),
            Shows("x, y, z = B      # ok: deconstruction unpacks B into x=1, y=2, z=3", "B = 1, 2, 3\nx, y, z = B\nx, y, z", "1\n2\n3"),
            Shows("x, y, z = B*     # also ok: supplies the same items", "B = 1, 2, 3\nx, y, z = B*\nx, y, z", "1\n2\n3"),
            Shows("x, *y = B        # x = 1, y = [2, 3]    (the collecting binding collects an exact list)", "B = 1, 2, 3\nx, *y = B\nx, y", "1\n[2, 3]"),
            Exempt("Collect(list) = list          # one ordinary argument boundary", "definition annotation; the prose after it states the claims"),
            Exempt("Collect(*values) = values     # collects the item supply as one list", "definition annotation; the prose after it states the claims"),
            Exempt("SequenceValueCount((*values)) = values.count # one sequence-value argument slot, then immediate contents", "definition annotation; the prose after it states the claims"),
            Shows("(Math.Pi, Math.Exp(1))       # (3.14, 2.72)", "DisplayDecimals = 2\n(Math.Pi, Math.Exp(1))", "(3.14, 2.72)"),
            Fails("Add(Pair)           # invalid: one argument expression", Slots + "Add(Pair)", KatLangErrorCode.ArityMismatch),
            Shows("Add(Pair[0], Pair[1]) # OK", Slots + "Add(Pair[0], Pair[1])", "30"),
            Fails("Use(1, Tail)        # invalid: two expression boundaries", Slots + "Use(1, Tail)", KatLangErrorCode.ArityMismatch),
            Shows("Use(1, Tail*)       # OK: Tail* spreads its items into the b and c slots", Slots + "Use(1, Tail*)", "6"),
            Shows("A*, 3                 # spread plus a separate slot: 1, 2, 3", "A = 1, 2\nA*, 3", "1\n2\n3"),
            Shows("(1, 2)*, 3            # 1, 2, 3", "(1, 2)*, 3", "1\n2\n3"),
            Shows("1*, (2, 3)            # 1, (2, 3) — spreading the scalar 1 yields one item; (2, 3) is a separate slot and stays one sequence value", "1*, (2, 3)", "1\n(2, 3)"),
            Shows("((1, 2))*, 3          # 1, 2, 3 — redundant unary parentheses normalize to (1, 2) before the spread opens its items", "((1, 2))*, 3", "1\n2\n3"),
            Shows("((1, 2), 3)*          # (1, 2), 3 — spread opens exactly one level; the inner pair stays intact", "((1, 2), 3)*", "(1, 2)\n3"),
            Shows("open A, B             # OK", "open A, B" + OpenPair + "X + Y", "3"),
            Rejects("open A*, B            # invalid: spread is not an open form", "open A*, B" + OpenPair + "1", KatLangErrorCode.BadOpenForm),
            Shows("[A*]                     # [1, 2, 3]", "A = 1, 2, 3\n[A*]", "[1, 2, 3]"),
            Shows("[0, A*, 4]               # [0, 1, 2, 3, 4]", "A = 1, 2, 3\n[0, A*, 4]", "[0, 1, 2, 3, 4]"),
            Shows("[1, []*, 2]              # [1, 2]", "[1, []*, 2]", "[1, 2]"),
            Exempt("State[1]              # found", "metavariable illustration: candidate and found name any state"),
            Shows("Values[1]              # 20", Selections + "Values[1]", "20"),
            Shows("Pairs[0]               # (1, 2)", Selections + "Pairs[0]", "(1, 2)"),
            Shows("Pairs[0][1]             # 2", Selections + "Pairs[0][1]", "2"),
            Shows("Rows[0]                # [1, 2]", Selections + "Rows[0]", "[1, 2]"),
            Shows("Rows[0][1]              # 2", Selections + "Rows[0][1]", "2"),
            Shows("range(1, 3)[2]         # 3", "range(1, 3)[2]", "3"),
            Shows("A.count              # 3", "A = 1, 2, 3\nA.count", "3"),
            Shows("().count             # 0   (the empty sequence value has zero items)", "().count", "0"),
            Shows("count(())            # 0", "count(())", "0"),
            Shows("(()).count           # 0   (redundant grouping normalizes to ())", "(()).count", "0"),
            Shows("U.count              # 2", "U = (1, 2, 3), 4\nU.count", "2"),
            Shows("T.count              # 3   (the lone grouped value is opened as the collection)", "T = (1, 2, 3)\nT.count", "3"),
            Fails("{}.count             # error", "{}.count", KatLangErrorCode.MissingOutput),
            Fails("count({})            # error", "count({})", KatLangErrorCode.MissingOutput),
            Shows("Add(3, 7)      # OK", "Add = a + b\nAdd(3, 7)", "10"),
            Shows("(3).Add(7)     # OK", "Add = a + b\n(3).Add(7)", "10"),
            Shows("A.KeepBoundary        # ((1, 2), 3)", "A = 1, 2\nKeepBoundary = a, 3\nA.KeepBoundary", "((1, 2), 3)"),
            Shows("A.JoinBoundary        # (1, 2, 3)", "A = 1, 2\nJoinBoundary = (a*, 3)\nA.JoinBoundary", "(1, 2, 3)"),
            Shows("Scale(Arg*, 10)    # spread the items into the collecting parameter: values = [1, 2, 3]; Scale(Arg, 10) passes ONE value, values = [(1, 2, 3)], which the numeric map rejects", Scale + "Scale(Arg*, 10)", "[10, 20, 30]"),
            Shows("(1, 2, 3)*.Scale(10)    # the spread receiver supplies its rows: values = [1, 2, 3], factor = 10", Scale + "(1, 2, 3)*.Scale(10)", "[10, 20, 30]"),
            Shows("Sum(Values*, 7)    # 37: spread opens two value slots, then 7 fills last", BackBound + "Sum(Values*, 7)", "37"),
            Shows("Sum(Values*)       # 30: the back-bound last takes 20, values = [10]", BackBound + "Sum(Values*)", "30"),
            Shows("count(Values)         # 3", Collections + "count(Values)", "3"),
            Shows("Values.count          # 3", Collections + "Values.count", "3"),
            Shows("count([1, 2, 3])      # 3 (a lone exact list opens the same way)", "count([1, 2, 3])", "3"),
            Fails("count(1, 2, 3)        # INVALID: arity error (three arguments)", "count(1, 2, 3)", KatLangErrorCode.ArityMismatch),
            Fails("count(Values*)        # INVALID: arity error (the spread supplies three arguments)", Collections + "count(Values*)", KatLangErrorCode.ArityMismatch),
            Shows("count((Values*, 8))     # 4", Collections + "count((Values*, 8))", "4"),
            Fails("count(Values*, 8)       # INVALID: arity error (four arguments)", Collections + "count(Values*, 8)", KatLangErrorCode.ArityMismatch),
            Shows("count((1, 2, 3))        # 3", "count((1, 2, 3))", "3"),
            Shows("sum((10, 20, 30))       # 60", "sum((10, 20, 30))", "60"),
            Shows("take((1, 2, 3), 2)      # [1, 2]", "take((1, 2, 3), 2)", "[1, 2]"),
            Shows("skip((1, 2, 3), 1)      # [2, 3]", "skip((1, 2, 3), 1)", "[2, 3]"),
            Shows("count((1, 2, 3))      # 3", "count((1, 2, 3))", "3"),
            Shows("T.count               # 3", "T = (1, 2, 3)\nT.count", "3"),
            Shows("(1, 2, 3).count       # 3", "(1, 2, 3).count", "3"),
            Shows("(1, 2, 3).sum         # 6", "(1, 2, 3).sum", "6"),
            Shows("((1, 2, 3)).count     # 3 (redundant grouping parentheses normalize away)", "((1, 2, 3)).count", "3"),
            Shows("A.count               # 3 (the lone list is opened as the collection)", "A = [1, 2, 3]\nA.count", "3"),
            Shows("sum([1, 2, 3])        # 6", "sum([1, 2, 3])", "6"),
            Shows("count(((1, 2), (3, 4)))   # 2", "count(((1, 2), (3, 4)))", "2"),
            Fails("count((1, 2), (3, 4))     # INVALID: arity error (two arguments)", "count((1, 2), (3, 4))", KatLangErrorCode.ArityMismatch),
            Exempt("Step(Pair).repeat(n)       # one state slot", "metavariable illustration: Step and n are placeholders"),
            Exempt("Step(Pair[0], Pair[1]).repeat(n)  # two state slots", "metavariable illustration: Step and n are placeholders"),
            Rejects("F(y) = 2             # invalid: same pattern shape as F(x) (duplicate branch)", DuplicateBranchProgram, KatLangErrorCode.DuplicateBranchPattern),
            Shows("Equal(x, x) = 1      # repeated-binder equality: matches only when both arguments are equal", EqualFamilyProgram, "1\n0"),
            Shows("Equal(x, y) = 0      # valid: distinct from the (x, x) equality constraint", EqualFamilyProgram, "1\n0"),
            Rejects("X                    # error: 'X' is ambiguous: 2 different opened algorithms provide it (A, B)", AmbiguousOpenProgram, KatLangErrorCode.AmbiguousOpen),
            Shows("Lib.UseHelper(10)    # 11", "Lib = {\n    UseHelper = x + 1\n}\nLib.UseHelper(10)", "11"),
            Shows("Pi                   # 3", OpenedPiProgram, "3"),
            Exempt("Lib = load('https://katlang.org/lib.kat')       # property definition", NetworkLoad),
            Exempt("open load('https://katlang.org/lib.kat')        # open list", NetworkLoad),
            Exempt("open 'https://katlang.org/lib.kat'              # shorthand for open load(...)", NetworkLoad),
            Exempt("Lib = load(Url)                                  # invalid: URL must be a literal, not a variable", RejectedLoad),
            Exempt("load('https://katlang.org/lib.kat')              # invalid: load is not allowed as runtime output", RejectedLoad),
            Exempt("Lib = load(\"https://katlang.org/{name}.kat\")     # invalid: a URL is fixed text, never interpolated", RejectedLoad),
        ],
    };

    [Theory]
    [MemberData(nameof(PromptFilePaths))]
    public void PromptFile_ContainsFreshGeneratedExamplesBlock(string relativePath)
    {
        var path = Path.Combine(RepoRoot.Find(), relativePath);
        Assert.True(File.Exists(path), $"{relativePath} not found.");

        var expectedBlock = RenderBlock();
        var raw = File.ReadAllText(path);
        var content = raw.ReplaceLineEndings("\n");
        var flag = RegenerationFlags.LanguageSpec;

        ArtifactRegeneration.VerifyOrRegenerate(
            flag,
            relativePath,
            regenerate: () =>
            {
                var updated = ReplaceOrAppendBlock(content, expectedBlock);
                // Preserve the file's existing line-ending convention.
                if (raw.Contains("\r\n", StringComparison.Ordinal))
                    updated = updated.Replace("\n", "\r\n", StringComparison.Ordinal);
                return updated;
            },
            verify: () =>
            {
                var begin = content.IndexOf(BeginMarker, StringComparison.Ordinal);
                var end = content.IndexOf(EndMarker, StringComparison.Ordinal);
                Assert.True(begin >= 0 && end > begin,
                    $"{relativePath} is missing the generated katlang-spec-examples block. " +
                    $"Set {flag}=1 and rerun this test to insert it (that run fails by design).");

                var actualBlock = content[begin..(end + EndMarker.Length)];
                Assert.True(expectedBlock == actualBlock,
                    $"{relativePath}: the generated katlang-spec-examples block is out of date with the canonical corpus. " +
                    $"Set {flag}=1 and rerun this test to regenerate it (that run fails by design), then review the diff.");
            });
    }

    [Theory]
    [MemberData(nameof(PromptFilePaths))]
    public void PromptFile_UsesOnlyCanonicalCollectingAndSpreadGuidance(string relativePath)
    {
        var content = File.ReadAllText(Path.Combine(RepoRoot.Find(), relativePath));

        // Collecting bindings: prefix `*name` is the one canonical spelling.
        Assert.Contains("*items", content, StringComparison.Ordinal);
        Assert.Contains("collecting parameter", content, StringComparison.OrdinalIgnoreCase);

        // Spreading: the attached postfix star marker producing a SUPPLY.
        Assert.Contains("items*", content, StringComparison.Ordinal);

        // The central multiplication-disambiguation rule must be stated.
        Assert.Contains("a*, b", content, StringComparison.Ordinal);

        // The canonical forwarding example must be present (fluent form).
        Assert.Contains(
            "Forward(*items) = items*.Target",
            content,
            StringComparison.Ordinal);
    }

    [Theory]
    [MemberData(nameof(PromptFilePaths))]
    public void PromptFile_RejectsStaleCanonicalSyntax(string relativePath)
    {
        var content = File.ReadAllText(Path.Combine(RepoRoot.Find(), relativePath));

        // The removed spellings must not be taught anywhere in the prompts:
        // no ellipsis collecting bindings and no reserved call/property spread form.
        Assert.DoesNotContain("items...", content, StringComparison.Ordinal);
        Assert.DoesNotContain("...items", content, StringComparison.Ordinal);
        // Any name directly joined to an ellipsis reads as the former binding whatever the
        // name (a corpus explanation once wrote the dot-call law as `F(args...)`), so the
        // check is by shape, not by the one spelling `items`.
        Assert.Empty(Regex.Matches(content, @"[A-Za-z_]\.\.\."));
        Assert.Empty(Regex.Matches(content, @"\.\.\.[A-Za-z_]"));
        Assert.DoesNotContain("spread(items)", content, StringComparison.Ordinal);
        Assert.DoesNotContain("items.spread", content, StringComparison.Ordinal);
        Assert.DoesNotContain(".spread", content, StringComparison.Ordinal);
        Assert.DoesNotContain("rest parameter", content, StringComparison.OrdinalIgnoreCase);
        Assert.DoesNotContain("rest binding", content, StringComparison.OrdinalIgnoreCase);
        Assert.DoesNotContain("variadic parameter", content, StringComparison.OrdinalIgnoreCase);

        // Explicit output syntax is gone: `Output` is an ordinary identifier, so the
        // prompts must not teach it as reserved result syntax or forbid ordinary use.
        Assert.DoesNotContain("Output = ...", content, StringComparison.Ordinal);
        Assert.DoesNotContain("reserved result syntax", content, StringComparison.OrdinalIgnoreCase);
        Assert.DoesNotContain("explicit output", content, StringComparison.OrdinalIgnoreCase);
        Assert.DoesNotContain("implicit output", content, StringComparison.OrdinalIgnoreCase);
    }

    [Theory]
    [MemberData(nameof(PromptFilePaths))]
    public void PromptFile_TeachesStringInterpolation_AndNoLongerForbidsDoubleQuotes(string relativePath)
    {
        var content = File.ReadAllText(Path.Combine(RepoRoot.Find(), relativePath));

        // STR-02: double-quoted strings, their escapes and interpolation are taught...
        Assert.Contains("interpolation hole", content, StringComparison.Ordinal);
        Assert.Contains("\"Hello, {name}!\"", content, StringComparison.Ordinal);
        Assert.Contains("{{", content, StringComparison.Ordinal);
        Assert.Contains("no format specifiers", content, StringComparison.Ordinal);

        // ...and the superseded claims (STR-01's single-quote-only strings, concatenation as the
        // unsupported exemplar) are gone.
        Assert.DoesNotContain("there are no double-quoted strings", content, StringComparison.OrdinalIgnoreCase);
        Assert.DoesNotContain("Do not invent double-quoted strings", content, StringComparison.Ordinal);
        Assert.DoesNotContain("string concatenation is not available", content, StringComparison.Ordinal);
    }

    private static string ReplaceOrAppendBlock(string content, string block)
    {
        var begin = content.IndexOf(BeginMarker, StringComparison.Ordinal);
        var end = content.IndexOf(EndMarker, StringComparison.Ordinal);
        if (begin >= 0 && end > begin)
            return content[..begin] + block + content[(end + EndMarker.Length)..];

        var trimmed = content.TrimEnd('\n');
        return trimmed + "\n\n" + block + "\n";
    }

    internal static string RenderBlock()
    {
        var cases = LanguageSpecCorpus.AllCases();
        var selected = cases.Where(c => c.IncludeInGeneratorPrompt).ToList();

        var builder = new StringBuilder();
        builder.Append(BeginMarker);
        builder.Append('\n');
        builder.Append($"""

            Verified reference examples ({selected.Count} of the {cases.Count}-case canonical language specification,
            tests/KatLang.Tests/LanguageSpec/LanguageSpecCorpus.cs). Every program and expected
            output below is executed against the KatLang engine and (where representable)
            guarded against the Lean model on every build. Treat these as ground truth for the
            language behaviors they demonstrate.

            Regenerate this block from the repo root with:
              $env:KATLANG_REGENERATE_LANGUAGE_SPEC = "1"
              dotnet test .\KatLang.slnx --filter LanguageSpecArtifacts

            """.ReplaceLineEndings("\n"));

        foreach (var specCase in selected)
        {
            builder.Append('\n');
            builder.Append($"[{specCase.Id}] {specCase.Explanation}\n\n");
            foreach (var line in specCase.Source.Split('\n'))
                builder.Append(line.Length == 0 ? "\n" : $"    {line}\n");

            switch (specCase.Outcome)
            {
                case SpecOutcome.Evaluates:
                    builder.Append("\n  Displays:\n");
                    foreach (var row in specCase.ExpectedDisplay!.Split('\n'))
                        builder.Append($"    {row}\n");
                    break;
                case SpecOutcome.EvalError:
                    builder.Append($"\n  Fails with an evaluation error ({specCase.ExpectedErrorCategory}).\n");
                    break;
                case SpecOutcome.ParseError:
                    builder.Append("\n  Rejected by the parser");
                    builder.Append(specCase.ExpectedParseDiagnosticFragment is { } fragment
                        ? $": \"{fragment} ...\"\n"
                        : ".\n");
                    break;
            }
        }

        builder.Append('\n');
        builder.Append(EndMarker);
        return builder.ToString();
    }
}
